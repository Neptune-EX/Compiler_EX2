#include "backend/generator.h"

#include <cassert>
#include <cstring>

backend::Generator::Generator(ir::Program &p, std::ofstream &f) : program(p), fout(f) {
    orCount = andCount = 0;  // 初始化计数器
}

void backend::Generator::gen() {
    emitOption();
    initGlobalVars(program.functions.front());
    emitText();
    for (size_t i = 1; i < program.functions.size(); i++)
        genFunc(program.functions[i]);
}

void backend::Generator::genFunc(const ir::Function &func) {
    emitGlobal(func.name);
    emitTypeFunc(func.name);
    emitLabel(func.name);

    int argCnt = saveReg(func);
    genJumpLabels(func);

    int idx = 0;
    for (const ir::Instruction *inst : func.InstVec) {
        if (labelMap.find(idx) != labelMap.end())
            emitLabel(labelMap[idx]);
        genInstr(*inst, idx++, argCnt);
    }

    fout << "\t.size\t" << func.name << ", .-" << func.name << "\n";
}

void backend::Generator::genInstr(const ir::Instruction &inst, int idx, int argCnt) {
    ir::Operator op = inst.op;
    if      (op == ir::Operator::_return)   genReturn(inst);
    else if (op == ir::Operator::call)      genCall(inst);
    else if (op == ir::Operator::def)       genDef(inst);
    else if (op == ir::Operator::fdef)      genFdef(inst);
    else if (op == ir::Operator::mov)       genMov(inst);
    else if (op == ir::Operator::fmov)      genFmov(inst);
    else if (op == ir::Operator::alloc)     genAlloc(inst);
    else if (op == ir::Operator::store)     genStore(inst, argCnt);
    else if (op == ir::Operator::load)      genLoad(inst, argCnt);
    else if (op == ir::Operator::getptr)    genGetptr(inst, argCnt);
    else if (op == ir::Operator::add)       genAdd(inst);
    else if (op == ir::Operator::fadd)      genFadd(inst);
    else if (op == ir::Operator::sub)       genSub(inst);
    else if (op == ir::Operator::fsub)      genFsub(inst);
    else if (op == ir::Operator::mul)       genMul(inst);
    else if (op == ir::Operator::fmul)      genFmul(inst);
    else if (op == ir::Operator::div)       genDiv(inst);
    else if (op == ir::Operator::fdiv)      genFdiv(inst);
    else if (op == ir::Operator::mod)       genMod(inst);
    else if (op == ir::Operator::eq)        genEq(inst);
    else if (op == ir::Operator::neq)       genNeq(inst);
    else if (op == ir::Operator::fneq)      genNeq(inst);
    else if (op == ir::Operator::lss)       genLss(inst);
    else if (op == ir::Operator::flss)      genFlss(inst);
    else if (op == ir::Operator::leq)       genLeq(inst);
    else if (op == ir::Operator::gtr)       genGtr(inst);
    else if (op == ir::Operator::geq)       genGeq(inst);
    else if (op == ir::Operator::_or)       genOr(inst);
    else if (op == ir::Operator::_and)      genAnd(inst);
    else if (op == ir::Operator::_goto)     genGoto(inst, idx);
    else if (op == ir::Operator::__unuse__) genUnuse(inst);
    else if (op == ir::Operator::cvt_i2f)   genCvtI2F(inst);
    else if (op == ir::Operator::cvt_f2i)   genCvtF2I(inst);
    else assert(0 && "to be continue");
}

int backend::Generator::saveReg(const ir::Function &func) {
    stackVarMap.clear();
    stackSize = 4;

    for (auto fParam : func.ParameterList)
        addOperand(fParam);

    for (auto inst : func.InstVec) {
        if (inst->des.type == ir::Type::Int || inst->des.type == ir::Type::Float) {
            if (!isGlobal(inst->des.name))
                addOperand(inst->des);
        } else if (inst->des.type == ir::Type::IntPtr && inst->op == ir::Operator::alloc
                   && inst->op1.type == ir::Type::IntLiteral) {
            addOperand(inst->des, stoi(inst->op1.name) * 4);
        } else if (inst->des.type == ir::Type::FloatPtr && inst->op == ir::Operator::alloc
                   && inst->op1.type == ir::Type::IntLiteral) {
            addOperand(inst->des, stoi(inst->op1.name) * 4);
        } else if (inst->des.type == ir::Type::IntPtr && inst->op == ir::Operator::getptr) {
            addOperand(inst->des);
        } else if (inst->des.type == ir::Type::FloatPtr && inst->op == ir::Operator::getptr) {
            addOperand(inst->des);
        }

        if (inst->op1.type == ir::Type::Int || inst->op1.type == ir::Type::Float) {
            if (!isGlobal(inst->op1.name))
                addOperand(inst->op1);
        }

        if (inst->op2.type == ir::Type::Int || inst->op2.type == ir::Type::Float) {
            if (!isGlobal(inst->op2.name))
                addOperand(inst->op2);
        }
    }

    // ==================== 关键修改：栈帧 16 字节对齐 ====================
    int aligned = (stackSize + 15) & ~15;
    if (aligned != stackSize) {
        stackSize = aligned;
    }
    // ==================================================================

    fout << "\taddi\tsp, sp, -" << stackSize << "\n";
    fout << "\tsw\tra, 0(sp)\n";

    for (int i = 0; i < (int)func.ParameterList.size(); i++) {
        if (i <= 7) {
            if (func.ParameterList[i].type == ir::Type::Float)
                fout << "\tfsw\tfa" << i << ", " << findOperand(func.ParameterList[i]) << "(sp)\n";
            else
                fout << "\tsw\ta" << i << ", " << findOperand(func.ParameterList[i]) << "(sp)\n";
        } else {
            if (i == 8)
                fout << "\taddi\tt2, sp, " << stackSize << "\n";
            fout << "\tlw\tt5, " << (i - 8) * 4 << "(t2)\n";
            fout << "\tsw\tt5, " << findOperand(func.ParameterList[i]) << "(sp)\n";
        }
    }

    return func.ParameterList.size();
}

void backend::Generator::genJumpLabels(const ir::Function &func) {
    labelMap.clear();
    labelCount = 0;
    for (int i = 0; i < (int)func.InstVec.size(); i++) {
        auto inst = func.InstVec[i];
        if (inst->op == ir::Operator::_goto) {
            int offset = std::stoi(inst->des.name);
            int idx = i + offset;
            if (labelMap.find(idx) == labelMap.end())
                labelMap[idx] = func.name + "_label_" + std::to_string(labelCount++);
        }
    }
}

void backend::Generator::recoverReg() {
    fout << "\tlw\tra, 0(sp)\n";
    fout << "\taddi\tsp,sp," << stackSize << "\n";
}

void backend::Generator::genReturn(const ir::Instruction &inst) {
    if (inst.op1.type == ir::Type::IntLiteral) {
        fout << "\tli\ta0, " << std::stoi(inst.op1.name) << "\n";
        recoverReg();
        fout << "\tjr\tra\n";
    } else if (inst.op1.type == ir::Type::Int) {
        if (isGlobal(inst.op1.name)) {
            fout << "\tlui\tt3, %hi(" << inst.op1.name << ")\n";
            fout << "\taddi\tt3, t3, %lo(" << inst.op1.name << ")\n";
            fout << "\tlw\ta0, 0(t3)" << "\n";
            recoverReg();
            fout << "\tjr\tra\n";
        } else {
            fout << "\tlw\ta0, " << findOperand(inst.op1) << "(sp)\n";
            recoverReg();
            fout << "\tjr\tra\n";
        }
    } else if (inst.op1.type == ir::Type::null) {
        recoverReg();
        fout << "\tjr\tra\n";
    } else if (inst.op1.type == ir::Type::Float) {
        fout << "\tflw\tfa0, " << findOperand(inst.op1) << "(sp)\n";
        recoverReg();
        fout << "\tjr\tra\n";
    } else {
        assert(0 && "to be continue");
    }
}

void backend::Generator::genCall(const ir::Instruction &inst) {
    if (inst.op1.name == "global")
        return;

    int extendSize = 0;
    const auto *callInst = dynamic_cast<const ir::CallInst *>(&inst);
    for (int i = 0; i < (int)callInst->argumentList.size(); i++) {
        if (i <= 7) {
            loadT5(callInst->argumentList[i]);
            if (callInst->argumentList[i].type == ir::Type::FloatLiteral)
                fout << "\tfmv.w.x\tfa" << i << ", t5\n";
            else if (callInst->argumentList[i].type == ir::Type::Float)
                fout << "\tflw\tfa" << i << ", " << findOperand(callInst->argumentList[i]) << "(sp)\n";
            else
                fout << "\tmv\ta" << i << ", t5\n";
        } else {
            if (i == 8) {
                extendSize = ((int)callInst->argumentList.size() - 8) * 4;
                fout << "\taddi\tsp, sp, -" << extendSize << "\n";
            }
            loadT5(callInst->argumentList[i]);
            fout << "\tsw\tt5, " << (i - 8) * 4 << "(sp)\n";
        }
    }
    fout << "\tcall\t" << inst.op1.name << "\n";
    if (extendSize > 0)
        fout << "\taddi\tsp, sp, " << extendSize << "\n";
    if (inst.des.name != "null") {
        if (inst.des.type == ir::Type::Int)
            fout << "\tsw\ta0, " << findOperand(inst.des) << "(sp)\n";
        else if (inst.des.type == ir::Type::Float)
            fout << "\tfsw\tfa0, " << findOperand(inst.des) << "(sp)\n";
        else
            assert(0 && "to be continue");
    }
}

void backend::Generator::genDef(const ir::Instruction &inst) {
    if (inst.op1.type == ir::Type::IntLiteral && inst.des.type == ir::Type::Int) {
        fout << "\tli\tt6, " << inst.op1.name << "\n";
        fout << "\tsw\tt6, " << findOperand(inst.des) << "(sp)" << "\n";
    } else {
        assert(0 && "to be continue");
    }
}

void backend::Generator::genFdef(const ir::Instruction &inst) {
    if (inst.op1.type == ir::Type::FloatLiteral && inst.des.type == ir::Type::Float) {
        float fval = std::stof(inst.op1.name);
        uint32_t hex;
        std::memcpy(&hex, &fval, sizeof(hex));
        fout << "\tli\tt6, " << hex << "\n";
        fout << "\tsw\tt6, " << findOperand(inst.des) << "(sp)" << "\n";
    } else {
        assert(0 && "to be continue");
    }
}

void backend::Generator::genMov(const ir::Instruction &inst) {
    if (inst.op1.type == ir::Type::Int && inst.des.type == ir::Type::Int) {
        if (isGlobal(inst.op1.name)) {
            fout << "\tlui\tt3, %hi(" << inst.op1.name << ")\n";
            fout << "\taddi\tt3, t3, %lo(" << inst.op1.name << ")\n";
            fout << "\tlw\tt6, 0(t3)" << "\n";
        } else {
            fout << "\tlw\tt6, " << findOperand(inst.op1) << "(sp)" << "\n";
        }
        if (isGlobal(inst.des.name)) {
            fout << "\tlui\tt3, %hi(" << inst.des.name << ")\n";
            fout << "\taddi\tt3, t3, %lo(" << inst.des.name << ")\n";
            fout << "\tsw\tt6, 0(t3)" << "\n";
        } else {
            fout << "\tsw\tt6, " << findOperand(inst.des) << "(sp)" << "\n";
        }
    } else {
        assert(0 && "to be continue");
    }
}

void backend::Generator::genFmov(const ir::Instruction &inst) {
    if (inst.op1.type == ir::Type::Float && inst.des.type == ir::Type::Float) {
        fout << "\tflw\tft6, " << findOperand(inst.op1) << "(sp)" << "\n";
        fout << "\tfsw\tft6, " << findOperand(inst.des) << "(sp)" << "\n";
    } else {
        assert(0 && "to be continue");
    }
}

void backend::Generator::genAlloc(const ir::Instruction &) {
    // space already allocated during saveReg
}

void backend::Generator::genStore(const ir::Instruction &inst, int argCnt) {
    if (isGlobal(inst.op1.name)) {
        loadT5(inst.des);
        fout << "\tlui\tt3, %hi(" << inst.op1.name << ")\n";
        fout << "\taddi\tt3, t3, %lo(" << inst.op1.name << ")\n";
        loadT4(inst.op2);
        fout << "\tslli\tt4, t4, 2\n";
        fout << "\tadd\tt3, t3, t4\n";
        fout << "\tsw\tt5, 0(t3)\n";
    } else if (findOperand(inst.op1) >= 4 + argCnt * 4) {
        if (inst.op2.type == ir::Type::Int && inst.des.type == ir::Type::Float) {
            loadT5(inst.des);
            loadT4(inst.op2);
            fout << "\tslli\tt4, t4, 2\n";
            fout << "\tadd\tt3, sp, t4\n";
            fout << "\tfsw\tft5, " << findOperand(inst.op1) << "(t3)\n";
        } else if (inst.op2.type == ir::Type::Int) {
            loadT5(inst.des);
            loadT4(inst.op2);
            fout << "\tslli\tt4, t4, 2\n";
            fout << "\tadd\tt3, sp, t4\n";
            fout << "\tsw\tt5, " << findOperand(inst.op1) << "(t3)\n";
        } else if (inst.op2.type == ir::Type::IntLiteral && inst.op1.type == ir::Type::IntPtr) {
            loadT5(inst.des);
            fout << "\tsw\tt5, " << findOperand(inst.op1) + stoi(inst.op2.name) * 4 << "(sp)\n";
        } else if (inst.op2.type == ir::Type::IntLiteral && inst.op1.type == ir::Type::FloatPtr) {
            loadT5(inst.des);
            fout << "\tfsw\tft5, " << findOperand(inst.op1) + stoi(inst.op2.name) * 4 << "(sp)\n";
        } else {
            assert(0 && "to be continue");
        }
    } else {
        loadT5(inst.des);
        loadT4(inst.op2);
        fout << "\tslli\tt4, t4, 2\n";
        fout << "\tlw\tt3, " << findOperand(inst.op1) << "(sp)\n";
        fout << "\tadd\tt3, t3, t4\n";
        fout << "\tsw\tt5, 0(t3)\n";
    }
}

void backend::Generator::genLoad(const ir::Instruction &inst, int argCnt) {
    if (isGlobal(inst.op1.name)) {
        fout << "\tlui\tt3, %hi(" << inst.op1.name << ")\n";
        fout << "\taddi\tt3, t3, %lo(" << inst.op1.name << ")\n";
        loadT4(inst.op2);
        fout << "\tslli\tt4, t4, 2\n";
        fout << "\tadd\tt3, t3, t4\n";
        fout << "\tlw\tt5, 0(t3)\n";
        storeT5(inst.des);
    } else if (findOperand(inst.op1) >= 4 + argCnt * 4) {
        if (inst.op1.type == ir::Type::IntPtr) {
            loadT4(inst.op2);
            fout << "\tslli\tt4, t4, 2\n";
            fout << "\tadd\tt3, sp, t4\n";
            fout << "\tlw\tt5, " << findOperand(inst.op1) << "(t3)\n";
            storeT5(inst.des);
        } else {
            loadT4(inst.op2);
            fout << "\tslli\tt4, t4, 2\n";
            fout << "\tadd\tt3, sp, t4\n";
            fout << "\tflw\tft5, " << findOperand(inst.op1) << "(t3)\n";
            storeT5(inst.des);
        }
    } else {
        loadT4(inst.op2);
        fout << "\tslli\tt4, t4, 2\n";
        fout << "\tlw\tt3, " << findOperand(inst.op1) << "(sp)\n";
        fout << "\tadd\tt3, t4, t3\n";
        fout << "\tlw\tt5, 0(t3)\n";
        storeT5(inst.des);
    }
}

void backend::Generator::genGetptr(const ir::Instruction &inst, int argCnt) {
    if (isGlobal(inst.op1.name)) {
        fout << "\tlui\tt3, %hi(" << inst.op1.name << ")\n";
        fout << "\taddi\tt3, t3, %lo(" << inst.op1.name << ")\n";
        loadT4(inst.op2);
        fout << "\tslli\tt4, t4, 2\n";
        fout << "\tadd\tt5, t3, t4\n";
        storeT5(inst.des);
    } else if (findOperand(inst.op1) >= 4 + argCnt * 4) {
        loadT4(inst.op2);
        fout << "\tslli\tt4, t4, 2\n";
        fout << "\tadd\tt5, sp, t4\n";
        fout << "\taddi\tt5, t5, " << findOperand(inst.op1) << "\n";
        storeT5(inst.des);
    } else {
        loadT4(inst.op2);
        fout << "\tslli\tt4, t4, 2\n";
        fout << "\tlw\tt5, " << findOperand(inst.op1) << "(sp)\n";
        fout << "\tadd\tt5, t5, t4\n";
        storeT5(inst.des);
    }
}

void backend::Generator::genAdd(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\tadd\t t5, t5, t4\n";
    storeT5(inst.des);
}

void backend::Generator::genFadd(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\tfadd.s\t ft5, ft5, ft4\n";
    storeT5(inst.des);
}

void backend::Generator::genSub(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\tsub\t t5, t5, t4\n";
    storeT5(inst.des);
}

void backend::Generator::genFsub(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\tfsub.s\t ft5, ft5, ft4\n";
    storeT5(inst.des);
}

void backend::Generator::genMul(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\tmul\t t5, t5, t4\n";
    storeT5(inst.des);
}

void backend::Generator::genFmul(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\tfmul.s\t ft5, ft5, ft4\n";
    storeT5(inst.des);
}

void backend::Generator::genDiv(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\tdiv\t t5, t5, t4\n";
    storeT5(inst.des);
}

void backend::Generator::genFdiv(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\tfdiv.s\t ft5, ft5, ft4\n";
    storeT5(inst.des);
}

void backend::Generator::genMod(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\trem\t t5, t5, t4\n";
    storeT5(inst.des);
}

void backend::Generator::genEq(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\txor\tt5, t5, t4\n";
    fout << "\tseqz\tt5, t5\n";
    storeT5(inst.des);
}

void backend::Generator::genNeq(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    if (inst.op1.type == ir::Type::Float) {
        fout << "\tfeq.s\tt5, ft5, ft4\n";
        fout << "\tseqz\tt5, t5\n";
        fout << "\tfcvt.s.w\tft5, t5\n";
    } else {
        fout << "\txor\tt5, t5, t4\n";
        fout << "\tseqz\tt5, t5\n";
        fout << "\tseqz\tt5, t5\n";
    }
    storeT5(inst.des);
}

void backend::Generator::genLss(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\tslt\t t5, t5, t4\n";
    storeT5(inst.des);
}

void backend::Generator::genFlss(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\tflt.s\tt5, ft5, ft4\n";
    fout << "\tfcvt.s.w\tft5, t5\n";
    storeT5(inst.des);
}

void backend::Generator::genLeq(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\tsgt\tt5, t5, t4\n";
    fout << "\tseqz\tt5, t5\n";
    storeT5(inst.des);
}

void backend::Generator::genGtr(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\tsgt\tt5, t5, t4\n";
    storeT5(inst.des);
}

void backend::Generator::genGeq(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    fout << "\tslt\tt5, t5, t4\n";
    fout << "\tseqz\tt5, t5\n";
    storeT5(inst.des);
}

void backend::Generator::genOr(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    std::string setTrue = ".or_set_true_" + std::to_string(orCount);
    std::string end     = ".or_end_" + std::to_string(orCount++);
    fout << "\tbnez\tt5, " << setTrue << "\n ";
    fout << "\tbnez\tt4, " << setTrue << "\n ";
    fout << "\tli\tt5, 0\n";
    fout << "\tj\t" << end << "\n";
    emitLabel(setTrue);
    fout << "\tli\tt5, 1\n";
    emitLabel(end);
    storeT5(inst.des);
}

void backend::Generator::genAnd(const ir::Instruction &inst) {
    loadT5(inst.op1);
    loadT4(inst.op2);
    std::string setFalse = ".and_set_false_" + std::to_string(andCount);
    std::string end      = ".and_end_" + std::to_string(andCount++);
    fout << "\tbeqz\tt5, " << setFalse << "\n ";
    fout << "\tbeqz\tt4, " << setFalse << "\n ";
    fout << "\tli\tt5, 1\n";
    fout << "\tj\t" << end << "\n";
    emitLabel(setFalse);
    fout << "\tli\tt5, 0\n";
    emitLabel(end);
    storeT5(inst.des);
}

void backend::Generator::genGoto(const ir::Instruction &inst, int idx) {
    int offset = std::stoi(inst.des.name);
    idx += offset;
    if (labelMap.find(idx) == labelMap.end())
        assert(0 && "don't have this inst label");

    if (inst.op1.name == "null") {
        fout << "\tj\t" << labelMap[idx] << "\n";
    } else {
        loadT5(inst.op1);
        if (inst.op1.type == ir::Type::Int)
            fout << "\tbne\tt5, zero, " << labelMap[idx] << "\n";
        else if (inst.op1.type == ir::Type::Float) {
            fout << "\tfmv.x.w\tt5, ft5\n";
            fout << "\tbne\tt5, zero, " << labelMap[idx] << "\n";
        }
    }
}

void backend::Generator::genUnuse(const ir::Instruction &) {
    fout << "\tnop\n";
}

void backend::Generator::genCvtI2F(const ir::Instruction &inst) {
    loadT5(inst.op1);
    fout << "\tcsrr\tt1, frm\n";
    fout << "\tli\tt0, 1\n";
    fout << "\tcsrw\tfrm, t0\n";
    fout << "\tfcvt.s.w\t ft5, t5\n";
    fout << "\tcsrw\tfrm, t1\n";
    storeT5(inst.des);
}

void backend::Generator::genCvtF2I(const ir::Instruction &inst) {
    loadT5(inst.op1);
    fout << "\tcsrr\tt1, frm\n";
    fout << "\tli\tt0, 1\n";
    fout << "\tcsrw\tfrm, t0\n";
    fout << "\tfcvt.w.s\t t5, ft5\n";
    fout << "\tcsrw\tfrm, t1\n";
    storeT5(inst.des);
}

void backend::Generator::loadT5(const ir::Operand &op) {
    if (isGlobal(op.name)) {
        if (op.type == ir::Type::Int) {
            fout << "\tlui\tt3, %hi(" << op.name << ")\n";
            fout << "\taddi\tt3, t3, %lo(" << op.name << ")\n";
            fout << "\tlw\tt5, 0(t3)\n";
        } else {
            assert(0 && "to be continue");
        }
    } else {
        if (op.type == ir::Type::Int) {
            fout << "\tlw\tt5, " << findOperand(op) << "(sp)\n";
        } else if (op.type == ir::Type::IntLiteral) {
            fout << "\tli\tt5, " << op.name << "\n";
        } else if (op.type == ir::Type::IntPtr || op.type == ir::Type::FloatPtr) {
            fout << "\tlw\tt5, " << findOperand(op) << "(sp)\n";
        } else if (op.type == ir::Type::Float) {
            fout << "\tflw\tft5, " << findOperand(op) << "(sp)\n";
        } else if (op.type == ir::Type::FloatLiteral) {
            if (op.name == "0.0") {
                fout << "\tli\tt5, 0\n";
                fout << "\tfmv.s.x\tft5, t5\n";
            } else {
                float fval = std::stof(op.name);
                uint32_t hex;
                std::memcpy(&hex, &fval, sizeof(hex));
                fout << "\tli\tt5, " << hex << "\n";
            }
        } else {
            assert(0 && "to be continue");
        }
    }
}

void backend::Generator::loadT4(const ir::Operand &op) {
    if (isGlobal(op.name)) {
        if (op.type == ir::Type::Int) {
            fout << "\tlui\tt3, %hi(" << op.name << ")\n";
            fout << "\taddi\tt3, t3, %lo(" << op.name << ")\n";
            fout << "\tlw\tt4, 0(t3)\n";
        } else {
            assert(0 && "to be continue");
        }
    } else {
        if (op.type == ir::Type::Int) {
            fout << "\tlw\tt4, " << findOperand(op) << "(sp)\n";
        } else if (op.type == ir::Type::IntLiteral) {
            fout << "\tli\tt4, " << op.name << "\n";
        } else if (op.type == ir::Type::Float) {
            fout << "\tflw\tft4, " << findOperand(op) << "(sp)\n";
        } else if (op.type == ir::Type::FloatLiteral) {
            if (op.name == "0.0") {
                fout << "\tli\tt4, 0\n";
                fout << "\tfmv.s.x\tft4, t4\n";
            } else {
                assert(0 && "to be continue");
            }
        } else {
            assert(0 && "to be continue");
        }
    }
}

void backend::Generator::storeT5(const ir::Operand &op) {
    if (op.type == ir::Type::Int || op.type == ir::Type::IntPtr || op.type == ir::Type::FloatPtr) {
        fout << "\tsw\tt5, " << findOperand(op) << "(sp)\n";
    } else if (op.type == ir::Type::Float) {
        fout << "\tfsw\tft5, " << findOperand(op) << "(sp)\n";
    } else {
        assert(0 && "to be continue");
    }
}

bool backend::Generator::isGlobal(const std::string &name) const {
    for (const auto &var : program.globalVal)
        if (var.val.name == name)
            return true;
    return false;
}

int backend::Generator::findOperand(ir::Operand opd) {
    if (stackVarMap.find(opd.name) == stackVarMap.end())
        assert(0 && "can not find opd in stack");
    return stackVarMap[opd.name];
}

void backend::Generator::addOperand(ir::Operand opd, uint32_t size) {
    if (stackVarMap.find(opd.name) == stackVarMap.end()) {
        stackVarMap[opd.name] = stackSize;
        stackSize += size;
    }
}

void backend::Generator::initGlobalVars(const ir::Function &func) {
    emitData();

    std::map<std::string, int> initVal;
    for (int i = 0; i < (int)func.InstVec.size(); i++) {
        if (func.InstVec[i]->op == ir::Operator::def) {
            ir::Instruction *defInst = func.InstVec[i];
            ir::Instruction *movInst = func.InstVec[i + 1];
            emitGlobal(movInst->des.name);
            emitTypeObj(movInst->des.name);
            fout << "\t.size\t" << movInst->des.name << ", 4\n";
            emitLabel(movInst->des.name);
            emitWord(defInst->op1.name);
            initVal[movInst->des.name] = 1;
            i++;
        } else if (func.InstVec[i]->op == ir::Operator::alloc) {
            ir::Instruction *allocInst = func.InstVec[i];
            emitGlobal(allocInst->des.name);
            emitTypeObj(allocInst->des.name);
            fout << "\t.size\t" << allocInst->des.name << ", " << stoi(allocInst->op1.name) * 4 << "\n";
            emitLabel(allocInst->des.name);
            initVal[allocInst->des.name] = 1;
            for (int j = i + 1; ; j++) {
                if (func.InstVec[j]->op == ir::Operator::store) {
                    ir::Instruction *storeInst = func.InstVec[j];
                    if (storeInst->des.type == ir::Type::IntLiteral)
                        emitWord(storeInst->des.name);
                    else
                        assert(0 && "to be continue");
                } else {
                    i = j - 1;
                    break;
                }
            }
        } else if (func.InstVec[i]->op == ir::Operator::_return) {
            break;
        } else {
            assert(0 && "to be continue");
        }
    }

    for (const auto &globalVar : program.globalVal) {
        if (initVal[globalVar.val.name] != 1) {
            if (globalVar.val.type == ir::Type::IntPtr)
                fout << "\t.comm\t" << globalVar.val.name << ", " << globalVar.maxlen * 4 << ", 4\n";
            else if (globalVar.val.type == ir::Type::Int)
                fout << "\t.comm\t" << globalVar.val.name << ", 4, 4\n";
            else
                assert(0 && "to be continue");
        }
    }
}

void backend::Generator::emitOption() {
    fout << "\t.option nopic\n";
}

void backend::Generator::emitText() {
    fout << "\t.text\n";
    fout << "\t.align\t1\n";
}

void backend::Generator::emitData() {
    fout << "\t.section\t.data\n";
    fout << "\t.align\t2\n";
}

void backend::Generator::emitGlobal(const std::string &name) {
    fout << "\t.global\t" << name << "\n";
}

void backend::Generator::emitTypeFunc(const std::string &name) {
    fout << "\t.type\t" << name << ", @function\n";
}

void backend::Generator::emitTypeObj(const std::string &name) {
    fout << "\t.type\t" << name << ", @object\n";
}

void backend::Generator::emitLabel(const std::string &name) {
    fout << name << ":\n";
}

void backend::Generator::emitWord(const std::string &val) {
    fout << "\t.word\t" << val << "\n";
}