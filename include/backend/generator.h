#ifndef GENERATOR_H
#define GENERATOR_H

#include "ir/ir.h"
#include "backend/rv_def.h"
#include "backend/rv_inst_impl.h"

#include <map>
#include <string>
#include <vector>
#include <fstream>

namespace backend {

struct Generator {
    const ir::Program &program;
    std::ofstream &fout;
    std::map<std::string, int> stackVarMap;
    int stackSize;
    std::map<int, std::string> labelMap;
    int labelCount;
    int orCount;
    int andCount;

    Generator(ir::Program &, std::ofstream &);

    void gen();
    void genFunc(const ir::Function &);
    void genInstr(const ir::Instruction &, int idx, int argCnt);

    int  saveReg(const ir::Function &);
    void genJumpLabels(const ir::Function &);
    void recoverReg();

    void genReturn(const ir::Instruction &);
    void genCall(const ir::Instruction &);
    void genDef(const ir::Instruction &);
    void genFdef(const ir::Instruction &);
    void genMov(const ir::Instruction &);
    void genFmov(const ir::Instruction &);
    void genAlloc(const ir::Instruction &);
    void genStore(const ir::Instruction &, int argCnt);
    void genLoad(const ir::Instruction &, int argCnt);
    void genGetptr(const ir::Instruction &, int argCnt);
    void genAdd(const ir::Instruction &);
    void genFadd(const ir::Instruction &);
    void genSub(const ir::Instruction &);
    void genFsub(const ir::Instruction &);
    void genMul(const ir::Instruction &);
    void genFmul(const ir::Instruction &);
    void genDiv(const ir::Instruction &);
    void genFdiv(const ir::Instruction &);
    void genMod(const ir::Instruction &);
    void genEq(const ir::Instruction &);
    void genNeq(const ir::Instruction &);
    void genLss(const ir::Instruction &);
    void genFlss(const ir::Instruction &);
    void genLeq(const ir::Instruction &);
    void genGtr(const ir::Instruction &);
    void genGeq(const ir::Instruction &);
    void genOr(const ir::Instruction &);
    void genAnd(const ir::Instruction &);
    void genGoto(const ir::Instruction &, int idx);
    void genUnuse(const ir::Instruction &);
    void genCvtI2F(const ir::Instruction &);
    void genCvtF2I(const ir::Instruction &);

    void loadT5(const ir::Operand &);
    void loadT4(const ir::Operand &);
    void storeT5(const ir::Operand &);

    bool isGlobal(const std::string &) const;
    int  findOperand(ir::Operand);
    void addOperand(ir::Operand, uint32_t size = 4);

    void initGlobalVars(const ir::Function &);
    void emitOption();
    void emitText();
    void emitData();
    void emitGlobal(const std::string &);
    void emitTypeFunc(const std::string &);
    void emitTypeObj(const std::string &);
    void emitLabel(const std::string &);
    void emitWord(const std::string &);
};

} // namespace backend

#endif