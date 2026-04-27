#include "front/semantic.h"

#include <cassert>

using ir::Function;
using ir::Instruction;
using ir::Operand;
using ir::Operator;

#define TODO assert(0 && "TODO");

#define MATCH_NODE_TYPE(node, index) root->children[index]->type == node

#define COPY_EXP_NODE(from, to) \
    to->v = from->v;            \
    to->t = from->t;

#define GET_NODE_PTR(type, node, index)                      \
    auto node = dynamic_cast<type *>(root->children[index]); \
    assert(node);

#define TOS(value) std::to_string(value)

map<std::string, ir::Function *> *frontend::get_lib_funcs()
{
    static map<std::string, ir::Function *> lib_funcs = {
        {"getint", new Function("getint", Type::Int)},
        {"getch", new Function("getch", Type::Int)},
        {"getfloat", new Function("getfloat", Type::Float)},
        {"getarray", new Function("getarray", {Operand("arr", Type::IntPtr)}, Type::Int)},
        {"getfarray", new Function("getfarray", {Operand("arr", Type::FloatPtr)}, Type::Int)},
        {"putint", new Function("putint", {Operand("i", Type::Int)}, Type::null)},
        {"putch", new Function("putch", {Operand("i", Type::Int)}, Type::null)},
        {"putfloat", new Function("putfloat", {Operand("f", Type::Float)}, Type::null)},
        {"putarray", new Function("putarray", {Operand("n", Type::Int), Operand("arr", Type::IntPtr)}, Type::null)},
        {"putfarray", new Function("putfarray", {Operand("n", Type::Int), Operand("arr", Type::FloatPtr)}, Type::null)},
    };
    return &lib_funcs;
}

frontend::STE::STE() {}

frontend::STE::STE(ir::Operand _operand, vector<int> _dimension, int _size, bool _isConst = false) : operand(_operand), dimension(_dimension), size(_size), isConst(_isConst), val(string()) {}

void frontend::SymbolTable::add_scope()
{

    ScopeInfo scopeInfo;
    scopeInfo.cnt = scope_stack.size();
    scopeInfo.name = "Scp" + std::to_string(scopeInfo.cnt);
    scope_stack.push_back(scopeInfo);
}

void frontend::SymbolTable::exit_scope()
{

    scope_stack.pop_back();
}

string frontend::SymbolTable::get_scoped_name(string id) const
{

    assert(id != "");
    return id + "_" + scope_stack.back().name;
}

frontend::STE frontend::SymbolTable::get_ste(string id) const
{

    for (auto scope = scope_stack.rbegin(); scope != scope_stack.rend(); scope++)
    {
        if (scope->table.find(id) != scope->table.end())
            return scope->table.find(id)->second;
    }
    assert(0 && "symbol not found");
}

frontend::Analyzer::Analyzer() : tmp_cnt(0), symbol_table() {}

ir::Program frontend::Analyzer::get_ir_program(CompUnit *root)
{

    ir::Program program;

    map<std::string, ir::Function *> libFuncs = *get_lib_funcs();
    for (auto libFunc = libFuncs.begin(); libFunc != libFuncs.end(); libFunc++)
    {
        symbol_table.functions[libFunc->first] = libFunc->second;
    }

    symbol_table.add_scope();

    analyzeCompUnit(root);

    for (auto it = symbol_table.scope_stack[0].table.begin(); it != symbol_table.scope_stack[0].table.end(); it++)
    {
        auto &ste = it->second;
        if (ste.dimension.size())
            program.globalVal.push_back({ste.operand, ste.size});
        else
        {
            if (ste.isConst == false)
                program.globalVal.push_back({ste.operand, 0});
        }
    }

    Function globalFunc("global", Type::null);
    globalFunc.InstVec = g_init_inst;
    globalFunc.addInst(new Instruction({}, {}, {}, {Operator::_return}));

    program.functions.push_back(globalFunc);

    for (auto libFunc = libFuncs.begin(); libFunc != libFuncs.end(); libFunc++)
    {
        symbol_table.functions.erase(libFunc->first);
    }
    for (auto func = symbol_table.functions.begin(); func != symbol_table.functions.end(); func++)
    {
        if (func->first == "main")
            func->second->InstVec.insert(func->second->InstVec.begin(), new ir::CallInst(Operand("global", Type::null), {}));
        program.functions.push_back(*func->second);
    }

    symbol_table.exit_scope();
    return program;
}

void frontend::Analyzer::analyzeCompUnit(CompUnit *root)
{

    if (MATCH_NODE_TYPE(NodeType::DECL, 0))
    {
        GET_NODE_PTR(Decl, decl, 0)
        analyzeDecl(decl, g_init_inst);
    }
    else if (MATCH_NODE_TYPE(NodeType::FUNCDEF, 0))
    {
        GET_NODE_PTR(FuncDef, funcDef, 0)
        analyzeFuncDef(funcDef);
    }
    else
        assert(0 && "analyzeCompUnit error");

    if (root->children.size() > 1)
    {
        GET_NODE_PTR(CompUnit, compUnit, 1)
        analyzeCompUnit(compUnit);
    }
}

void frontend::Analyzer::analyzeDecl(Decl *root, vector<ir::Instruction *> &buffer)
{

    if (MATCH_NODE_TYPE(NodeType::CONSTDECL, 0))
    {
        GET_NODE_PTR(ConstDecl, constDecl, 0)
        analyzeConstDecl(constDecl, buffer);
    }
    else if (MATCH_NODE_TYPE(NodeType::VARDECL, 0))
    {
        GET_NODE_PTR(VarDecl, varDecl, 0)
        analyzeVarDecl(varDecl, buffer);
    }
    else
        assert(0 && "analyzeDecl error");
}

void frontend::Analyzer::analyzeFuncDef(FuncDef *root)
{

    GET_NODE_PTR(FuncType, funcType, 0)
    analyzeFuncType(funcType);
    GET_NODE_PTR(Term, funcName, 1)
    analyzeTerm(funcName);
    symbol_table.add_scope();
    vector<ir::Operand> fParams;
    if (MATCH_NODE_TYPE(NodeType::FUNCFPARAMS, 3))
    {
        GET_NODE_PTR(FuncFParams, funcFParams, 3)
        analyzeFuncFParams(funcFParams, fParams);
    }
    curFuncPtr = new Function(funcName->v, fParams, funcType->t);
    symbol_table.functions[funcName->v] = curFuncPtr;

    GET_NODE_PTR(Block, block, root->children.size() - 1)
    analyzeBlock(block, curFuncPtr->InstVec);

    symbol_table.exit_scope();

    if (curFuncPtr->InstVec.back()->op != Operator::_return)
    {

        if (funcType->t == ir::Type::null)
            curFuncPtr->addInst(new Instruction({}, {}, {}, Operator::_return));

        else if (funcName->v == "main")
            curFuncPtr->addInst(new Instruction({"0", ir::Type::IntLiteral}, {}, {}, {Operator::_return}));

    }
}

void frontend::Analyzer::analyzeFuncType(FuncType *root)
{

    GET_NODE_PTR(Term, term, 0)
    if (term->token.type == TokenType::VOIDTK)
        root->t = Type::null;
    else if (term->token.type == TokenType::INTTK)
        root->t = Type::Int;
    else if (term->token.type == TokenType::FLOATTK)
        root->t = Type::Float;
    else
        assert(0 && "analyzeFuncType error");
}

void frontend::Analyzer::analyzeTerm(Term *root)
{

    root->v = root->token.value;
}

void frontend::Analyzer::analyzeFuncFParams(FuncFParams *root, vector<ir::Operand> &fParams)
{

    for (int i = 0; i < root->children.size(); i += 2)
    {
        GET_NODE_PTR(FuncFParam, funcFParam, i)
        analyzeFuncFParam(funcFParam, fParams);
    }
}

void frontend::Analyzer::analyzeFuncFParam(FuncFParam *root, vector<ir::Operand> &fParams)
{

    GET_NODE_PTR(BType, bType, 0)
    analyzeBType(bType);
    GET_NODE_PTR(Term, varName, 1)
    analyzeTerm(varName);
    std::string varScpName = symbol_table.get_scoped_name(varName->v);

    vector<int> dimension;
    int size;
    if (root->children.size() > 2)
    {

        if (bType->t == Type::Int)
        {
            bType->t = Type::IntPtr;
        }
        else
        {
            bType->t = Type::FloatPtr;
        }
        size = -1;
        dimension.push_back(-1);
        for (int i = 5; i < root->children.size(); i += 2)
        {
            GET_NODE_PTR(ConstExp, constExp, i)
            analyzeConstExp(constExp);
            dimension.push_back(std::stoi(constExp->v));
            size *= std::stoi(constExp->v);
        }
    }
    else
        size = 0;

    symbol_table.scope_stack.back().table[varName->v] = STE({varScpName, bType->t}, {dimension}, size);
    fParams.push_back({varScpName, bType->t});
}

void frontend::Analyzer::analyzeBlock(Block *root, vector<ir::Instruction *> &buffer)
{

    for (int i = 1; i < root->children.size() - 1; i++)
    {
        GET_NODE_PTR(BlockItem, blockItem, i)
        analyzeBlockItem(blockItem, buffer);
    }
}

void frontend::Analyzer::analyzeBlockItem(BlockItem *root, vector<ir::Instruction *> &buffer)
{

    if (MATCH_NODE_TYPE(NodeType::DECL, 0))
    {
        GET_NODE_PTR(Decl, decl, 0)
        analyzeDecl(decl, buffer);
    }
    else if (MATCH_NODE_TYPE(NodeType::STMT, 0))
    {
        GET_NODE_PTR(Stmt, stmt, 0)
        analyzeStmt(stmt, buffer);
    }
    else
        assert(0 && "analyzeBlockItem error");
}

void frontend::Analyzer::analyzeStmt(Stmt *root, vector<ir::Instruction *> &buffer)
{

    if (MATCH_NODE_TYPE(NodeType::LVAL, 0))
    {
        GET_NODE_PTR(LVal, lVal, 0)
        analyzeLVal(lVal, buffer);
        GET_NODE_PTR(Exp, exp, 2)
        analyzeExp(exp, buffer);

        Operand lValVar = Operand(lVal->v, lVal->t);
        Operand rValVar;
        if (exp->t == Type::IntLiteral)
        {
            rValVar = IntLiteral2Int(exp->v, buffer);
        }
        else if (exp->t == Type::FloatLiteral)
        {
            rValVar = FloatLiteral2Float(exp->v, buffer);
        }
        else
        {
            rValVar = Operand(exp->v, exp->t);
        }

        if (lValVar.type == Type::Int || lValVar.type == Type::Float)
        {
            if (lValVar.type == Type::Int && rValVar.type == Type::Int)
            {
                buffer.push_back(new Instruction({rValVar}, {}, {lValVar}, {Operator::mov}));
            }
            else
            {
                assert(0 && "to be continue");
            }
        }
        else if (lValVar.type == Type::IntPtr || lValVar.type == Type::FloatPtr)
        {
            Operand offsetVar = Operand(lVal->offset, Type::Int);
            buffer.push_back(new Instruction({lValVar}, {offsetVar}, {rValVar}, {Operator::store}));
        }
        else
            assert(0 && "lVal type error");
    }
    else if (MATCH_NODE_TYPE(NodeType::BLOCK, 0))
    {

        symbol_table.add_scope();
        GET_NODE_PTR(Block, block, 0)
        analyzeBlock(block, buffer);
        symbol_table.exit_scope();
    }
    else if (MATCH_NODE_TYPE(NodeType::TERMINAL, 0))
    {
        GET_NODE_PTR(Term, term, 0)
        if (term->token.type == TokenType::IFTK)
        {
            GET_NODE_PTR(Cond, cond, 2)
            analyzeCond(cond, buffer);

            vector<Instruction *> ifInst;
            GET_NODE_PTR(Stmt, stmt, 4)
            analyzeStmt(stmt, ifInst);

            if (cond->t == Type::IntLiteral || cond->t == Type::FloatLiteral)
            {

                if ((cond->t == Type::IntLiteral && std::stoi(cond->v) != 0) || (cond->t == Type::FloatLiteral && std::stof(cond->v) != 0))
                {
                    buffer.insert(buffer.end(), ifInst.begin(), ifInst.end());
                }
                else
                {
                    if (root->children.size() > 5)
                    {
                        GET_NODE_PTR(Stmt, stmt, 6)
                        analyzeStmt(stmt, buffer);
                    }
                }
            }
            else
            {

                if (cond->t == Type::Float)
                {

                    Operand tmpVar = Operand(getTmp(), Type::Float);
                    buffer.push_back(new Instruction({cond->v, cond->t}, {"0.0", Type::FloatLiteral}, {tmpVar}, {Operator::fneq}));
                    buffer.push_back(new Instruction({tmpVar}, {}, {"2", Type::IntLiteral}, {Operator::_goto}));
                }
                else
                {
                    buffer.push_back(new Instruction({cond->v, cond->t}, {}, {"2", Type::IntLiteral}, {Operator::_goto}));
                }

                if (root->children.size() > 5)
                {
                    buffer.push_back(new Instruction({}, {}, {TOS(ifInst.size() + 2), Type::IntLiteral}, {Operator::_goto}));
                    buffer.insert(buffer.end(), ifInst.begin(), ifInst.end());

                    vector<Instruction *> elseInst;
                    GET_NODE_PTR(Stmt, stmt, 6)
                    analyzeStmt(stmt, elseInst);
                    buffer.push_back(new Instruction({}, {}, {TOS(elseInst.size() + 1), Type::IntLiteral}, {Operator::_goto}));
                    buffer.insert(buffer.end(), elseInst.begin(), elseInst.end());
                }
                else
                {
                    buffer.push_back(new Instruction({}, {}, {TOS(ifInst.size() + 1), Type::IntLiteral}, {Operator::_goto}));
                    buffer.insert(buffer.end(), ifInst.begin(), ifInst.end());
                }
                buffer.push_back(new Instruction({}, {}, {}, {Operator::__unuse__}));
            }
        }
        else if (term->token.type == TokenType::WHILETK)
        {

            int pos = buffer.size();
            GET_NODE_PTR(Cond, cond, 2)
            analyzeCond(cond, buffer);

            vector<Instruction *> whileInst;
            GET_NODE_PTR(Stmt, stmt, 4)
            analyzeStmt(stmt, whileInst);

            if (cond->t == Type::Int || cond->t == Type::Float)
            {
                if (cond->t == Type::Int)
                {
                    buffer.push_back(new Instruction({cond->v, cond->t}, {}, {"2", Type::IntLiteral}, {Operator::_goto}));
                }
                else
                {
                    assert(0 && "to be continue");
                }
                buffer.push_back(new Instruction({}, {}, {TOS(whileInst.size() + 2), Type::IntLiteral}, {Operator::_goto}));
            }

            for (int i = 0; i < whileInst.size(); i++)
            {
                if (whileInst[i]->op1.name == "break")
                {
                    whileInst[i] = new Instruction({}, {}, {TOS(whileInst.size() - i + 1), Type::IntLiteral}, {Operator::_goto});
                }
                else if (whileInst[i]->op1.name == "continue")
                {
                    whileInst[i] = new Instruction({}, {}, {TOS(pos - int(buffer.size()) - i), Type::IntLiteral}, {Operator::_goto});
                }
            }

            if (cond->t == Type::IntLiteral || cond->t == Type::FloatLiteral)
            {

                if ((cond->t == Type::IntLiteral && std::stoi(cond->v) != 0) || (cond->t == Type::FloatLiteral && std::stof(cond->v) != 0))
                {
                    buffer.insert(buffer.end(), whileInst.begin(), whileInst.end());
                    buffer.push_back(new Instruction({}, {}, {TOS(-int(whileInst.size())), Type::IntLiteral}, {Operator::_goto}));
                }
            }
            else
            {
                buffer.insert(buffer.end(), whileInst.begin(), whileInst.end());
                buffer.push_back(new Instruction({}, {}, {TOS(pos - int(buffer.size())), Type::IntLiteral}, {Operator::_goto}));
                buffer.push_back(new Instruction({}, {}, {}, {Operator::__unuse__}));
            }
        }

        else if (term->token.type == TokenType::BREAKTK)
        {
            buffer.push_back(new Instruction({"break"}, {}, {}, {Operator::__unuse__}));
        }
        else if (term->token.type == TokenType::CONTINUETK)
        {
            buffer.push_back(new Instruction({"continue"}, {}, {}, {Operator::__unuse__}));
        }
        else if (term->token.type == TokenType::RETURNTK)
        {
            if (root->children.size() == 2)
            {
                buffer.push_back(new Instruction({}, {}, {}, {Operator::_return}));
            }
            else if (MATCH_NODE_TYPE(NodeType::EXP, 1))
            {
                GET_NODE_PTR(Exp, exp, 1)
                analyzeExp(exp, buffer);

                if (curFuncPtr->returnType == Type::Int)
                {
                    if (exp->t == Type::Int || exp->t == Type::IntLiteral)
                    {
                        buffer.push_back(new Instruction({exp->v, exp->t}, {}, {}, {Operator::_return}));
                    }
                    else if (exp->t == Type::FloatLiteral)
                    {
                        exp->v = TOS(int(std::stof(exp->v)));
                        exp->t = Type::IntLiteral;
                        buffer.push_back(new Instruction({exp->v, exp->t}, {}, {}, {Operator::_return}));
                    }
                    else
                    {
                        assert(0 && "to be continue");
                    }
                }
                else if (curFuncPtr->returnType == Type::Float)
                {
                    if (exp->t == Type::Float || exp->t == Type::FloatLiteral)
                    {
                        buffer.push_back(new Instruction({exp->v, exp->t}, {}, {}, {Operator::_return}));
                    }
                    else
                    {
                        assert(0 && "to be continue");
                    }
                }
                else
                {
                    assert(0 && "to be continue");
                }
            }
            else
                assert(0 && "function return error");
        }
    }
    else
    {
        if (root->children.size() > 1)
        {
            GET_NODE_PTR(Exp, exp, 0)
            analyzeExp(exp, buffer);
        }
    }
}

void frontend::Analyzer::analyzeExp(Exp *root, vector<ir::Instruction *> &buffer)
{

    GET_NODE_PTR(AddExp, addExp, 0)
    analyzeAddExp(addExp, buffer);
    COPY_EXP_NODE(addExp, root)
}

void frontend::Analyzer::analyzeAddExp(AddExp *root, vector<ir::Instruction *> &buffer)
{

    GET_NODE_PTR(MulExp, mulExp1, 0)
    analyzeMulExp(mulExp1, buffer);

    int idx = -1;

    if (mulExp1->t == Type::IntLiteral || mulExp1->t == Type::FloatLiteral)
    {
        for (int i = 2; i < root->children.size(); i += 2)
        {
            vector<Instruction *> mulInst;
            GET_NODE_PTR(Term, term, i - 1)
            GET_NODE_PTR(MulExp, mulExp2, i)
            analyzeMulExp(mulExp2, mulInst);
            if (mulExp2->t == Type::IntLiteral || mulExp2->t == Type::FloatLiteral)
            {
                if (mulExp1->t == Type::IntLiteral && mulExp2->t == Type::IntLiteral)
                {
                    if (term->token.type == TokenType::PLUS)
                    {
                        mulExp1->v = TOS(std::stoi(mulExp1->v) + std::stoi(mulExp2->v));
                    }
                    else if (term->token.type == TokenType::MINU)
                    {
                        mulExp1->v = TOS(std::stoi(mulExp1->v) - std::stoi(mulExp2->v));
                    }
                    else
                        assert(0 && "AddExp op error");
                }
                else if (mulExp1->t == Type::IntLiteral && mulExp2->t == Type::FloatLiteral)
                {
                    mulExp1->t = Type::FloatLiteral;
                    if (term->token.type == TokenType::PLUS)
                    {
                        mulExp1->v = TOS(std::stoi(mulExp1->v) + std::stof(mulExp2->v));
                    }
                    else if (term->token.type == TokenType::MINU)
                    {
                        mulExp1->v = TOS(std::stoi(mulExp1->v) - std::stof(mulExp2->v));
                    }
                    else
                        assert(0 && "AddExp op error");
                }
                else if (mulExp1->t == Type::FloatLiteral && mulExp2->t == Type::IntLiteral)
                {
                    if (term->token.type == TokenType::PLUS)
                    {
                        mulExp1->v = TOS(std::stof(mulExp1->v) + std::stoi(mulExp2->v));
                    }
                    else if (term->token.type == TokenType::MINU)
                    {
                        mulExp1->v = TOS(std::stof(mulExp1->v) - std::stoi(mulExp2->v));
                    }
                    else
                        assert(0 && "AddExp op error");
                }
                else
                {
                    if (term->token.type == TokenType::PLUS)
                    {
                        mulExp1->v = TOS(std::stof(mulExp1->v) + std::stof(mulExp2->v));
                    }
                    else if (term->token.type == TokenType::MINU)
                    {
                        mulExp1->v = TOS(std::stof(mulExp1->v) - std::stof(mulExp2->v));
                    }
                    else
                        assert(0 && "AddExp op error");
                }
            }
            else
            {
                idx = i;
                break;
            }
        }
    }

    if ((mulExp1->t == Type::IntLiteral || mulExp1->t == Type::FloatLiteral) && idx == -1)
    {
        COPY_EXP_NODE(mulExp1, root)
    }
    else
    {
        Operand op1;
        if (idx == -1)
        {
            op1.name = mulExp1->v;
            op1.type = mulExp1->t;
            idx = 2;
        }
        else
        {
            if (mulExp1->t == Type::IntLiteral)
            {
                op1 = IntLiteral2Int(mulExp1->v, buffer);
            }
            else
            {
                op1 = FloatLiteral2Float(mulExp1->v, buffer);
            }
        }

        if (root->children.size() > 1)
        {
            if ((op1.type == Type::Int || op1.type == Type::Float) && op1.name.find('_') != op1.name.npos)
            {
                auto tmpVar = Operand(getTmp(), op1.type == Type::Int ? Type::Int : Type::Float);
                Operator cal = (op1.type == Type::Int) ? Operator::mov : Operator::fmov;
                buffer.push_back(new Instruction(op1, {}, tmpVar, cal));
                std::swap(op1, tmpVar);
            }
            for (int i = idx; i < root->children.size(); i += 2)
            {
                GET_NODE_PTR(Term, term, i - 1)
                GET_NODE_PTR(MulExp, mulExp2, i)
                analyzeMulExp(mulExp2, buffer);
                Operand op2;
                if (mulExp2->t == Type::IntLiteral)
                {
                    op2 = IntLiteral2Int(mulExp2->v, buffer);
                }
                else if (mulExp2->t == Type::FloatLiteral)
                {
                    op2 = FloatLiteral2Float(mulExp2->v, buffer);
                }
                else
                {
                    op2 = Operand(mulExp2->v, mulExp2->t);
                }

                if (term->token.type == TokenType::PLUS)
                {
                    if (op1.type == Type::Int && op2.type == Type::Int)
                    {
                        buffer.push_back(new Instruction(op1, op2, op1, Operator::add));
                    }
                    else if (op1.type == Type::Float && op2.type == Type::Float)
                    {

                        buffer.push_back(new Instruction(op1, op2, op1, Operator::fadd));
                    }
                    else
                    {
                        assert(0 && "to be continue");
                    }
                }
                else if (term->token.type == TokenType::MINU)
                {
                    if (op1.type == Type::Int && op2.type == Type::Int)
                    {
                        buffer.push_back(new Instruction(op1, op2, op1, Operator::sub));
                    }
                    else if (op1.type == Type::Float && op2.type == Type::Float)
                    {

                        buffer.push_back(new Instruction(op1, op2, op1, Operator::fsub));
                    }
                    else
                    {
                        assert(0 && "to be continue");
                    }
                }
                else
                    assert(0 && "AddExp op error");
            }
        }

        root->t = op1.type;
        root->v = op1.name;
    }
}

void frontend::Analyzer::analyzeMulExp(MulExp *root, vector<ir::Instruction *> &buffer)
{

    GET_NODE_PTR(UnaryExp, unaryExp1, 0)
    analyzeUnaryExp(unaryExp1, buffer);

    int idx = -1;

    if (unaryExp1->t == Type::IntLiteral || unaryExp1->t == Type::FloatLiteral)
    {
        for (int i = 2; i < root->children.size(); i += 2)
        {
            vector<Instruction *> unaryExpInst;
            GET_NODE_PTR(Term, term, i - 1)
            GET_NODE_PTR(UnaryExp, unaryExp2, i)
            analyzeUnaryExp(unaryExp2, unaryExpInst);
            if (unaryExp2->t == Type::IntLiteral || unaryExp2->t == Type::FloatLiteral)
            {
                if (unaryExp1->t == Type::IntLiteral && unaryExp2->t == Type::IntLiteral)
                {
                    if (term->token.type == TokenType::MULT)
                    {
                        unaryExp1->v = TOS(std::stoi(unaryExp1->v) * std::stoi(unaryExp2->v));
                    }
                    else if (term->token.type == TokenType::DIV)
                    {
                        unaryExp1->v = TOS(std::stoi(unaryExp1->v) / std::stoi(unaryExp2->v));
                    }
                    else if (term->token.type == TokenType::MOD)
                    {
                        unaryExp1->v = TOS(std::stoi(unaryExp1->v) % std::stoi(unaryExp2->v));
                    }
                    else
                        assert(0 && "MulExp op error");
                }
                else if (unaryExp1->t == Type::IntLiteral && unaryExp2->t == Type::FloatLiteral)
                {
                    unaryExp1->t = Type::FloatLiteral;
                    if (term->token.type == TokenType::MULT)
                    {
                        unaryExp1->v = TOS(std::stoi(unaryExp1->v) * std::stof(unaryExp2->v));
                    }
                    else if (term->token.type == TokenType::DIV)
                    {
                        unaryExp1->v = TOS(std::stoi(unaryExp1->v) / std::stof(unaryExp2->v));
                    }

                    else
                        assert(0 && "MulExp op error");
                }
                else if (unaryExp1->t == Type::FloatLiteral && unaryExp2->t == Type::IntLiteral)
                {
                    if (term->token.type == TokenType::MULT)
                    {
                        unaryExp1->v = TOS(std::stof(unaryExp1->v) * std::stoi(unaryExp2->v));
                    }
                    else if (term->token.type == TokenType::DIV)
                    {
                        unaryExp1->v = TOS(std::stof(unaryExp1->v) / std::stoi(unaryExp2->v));
                    }
                    else
                        assert(0 && "MulExp op error");
                }
                else
                {
                    if (term->token.type == TokenType::MULT)
                    {
                        unaryExp1->v = TOS(std::stof(unaryExp1->v) * std::stof(unaryExp2->v));
                    }
                    else if (term->token.type == TokenType::DIV)
                    {
                        unaryExp1->v = TOS(std::stof(unaryExp1->v) / std::stof(unaryExp2->v));
                    }
                    else
                        assert(0 && "MulExp op error");
                }
            }
            else
            {
                idx = i;
                break;
            }
        }
    }

    if ((unaryExp1->t == Type::IntLiteral || unaryExp1->t == Type::FloatLiteral) && idx == -1)
    {
        COPY_EXP_NODE(unaryExp1, root)
    }
    else
    {
        Operand op1;
        if (idx == -1)
        {
            op1.name = unaryExp1->v;
            op1.type = unaryExp1->t;
            idx = 2;
        }
        else
        {
            if (unaryExp1->t == Type::IntLiteral)
            {
                op1 = IntLiteral2Int(unaryExp1->v, buffer);
            }
            else
            {
                op1 = FloatLiteral2Float(unaryExp1->v, buffer);
            }
        }

        if (root->children.size() > 1)
        {
            if ((op1.type == Type::Int || op1.type == Type::Float) && op1.name.find('_') != op1.name.npos)
            {
                auto tmpVar = Operand(getTmp(), op1.type == Type::Int ? Type::Int : Type::Float);
                Operator cal = (op1.type == Type::Int) ? Operator::mov : Operator::fmov;
                buffer.push_back(new Instruction(op1, {}, tmpVar, cal));
                std::swap(op1, tmpVar);
            }
            for (int i = idx; i < root->children.size(); i += 2)
            {
                GET_NODE_PTR(Term, term, i - 1)
                GET_NODE_PTR(UnaryExp, unaryExp2, i)
                analyzeUnaryExp(unaryExp2, buffer);
                Operand op2;
                if (unaryExp2->t == Type::IntLiteral)
                {
                    op2 = IntLiteral2Int(unaryExp2->v, buffer);
                }
                else if (unaryExp2->t == Type::FloatLiteral)
                {
                    op2 = FloatLiteral2Float(unaryExp2->v, buffer);
                }
                else
                {
                    op2 = Operand(unaryExp2->v, unaryExp2->t);
                }

                if (term->token.type == TokenType::MULT)
                {
                    if (op1.type == Type::Int && op2.type == Type::Int)
                    {
                        buffer.push_back(new Instruction(op1, op2, op1, Operator::mul));
                    }
                    else if (op1.type == Type::Float && op2.type == Type::Float)
                    {

                        buffer.push_back(new Instruction(op1, op2, op1, Operator::fmul));
                    }
                    else if (op1.type == Type::Float && op2.type == Type::Int)
                    {

                        Operand tmpVar = Operand(getTmp(), Type::Float);
                        buffer.push_back(new Instruction({op2}, {}, {tmpVar}, {Operator::cvt_i2f}));
                        buffer.push_back(new Instruction({op1}, {tmpVar}, {op1}, {Operator::fmul}));
                    }
                    else if (op1.type == Type::Int && op2.type == Type::Float)
                    {

                        Operand tmpVar = Operand(getTmp(), Type::Float);
                        buffer.push_back(new Instruction({op1}, {}, {tmpVar}, {Operator::cvt_i2f}));
                        buffer.push_back(new Instruction({op2}, {tmpVar}, {op2}, {Operator::fmul}));
                        std::swap(op1, op2);
                    }
                    else
                    {
                        assert(0 && "to be continue");
                    }
                }
                else if (term->token.type == TokenType::DIV)
                {
                    if (op1.type == Type::Int && op2.type == Type::Int)
                    {
                        buffer.push_back(new Instruction(op1, op2, op1, Operator::div));
                    }
                    else if (op1.type == Type::Float && op2.type == Type::Int)
                    {

                        Operand tmpVar = Operand(getTmp(), Type::Float);
                        buffer.push_back(new Instruction({op2}, {}, {tmpVar}, {Operator::cvt_i2f}));
                        buffer.push_back(new Instruction({op1}, {tmpVar}, {op1}, {Operator::fdiv}));
                    }
                    else
                    {
                        assert(0 && "to be continue");
                    }
                }
                else if (term->token.type == TokenType::MOD)
                {
                    if (op1.type == Type::Int && op2.type == Type::Int)
                    {
                        buffer.push_back(new Instruction(op1, op2, op1, Operator::mod));
                    }
                    else
                    {
                        assert(0 && "% type error");
                    }
                }
                else
                    assert(0 && "MulExp op error");
            }
        }

        root->t = op1.type;
        root->v = op1.name;
    }
}

void frontend::Analyzer::analyzeUnaryExp(UnaryExp *root, vector<ir::Instruction *> &buffer)
{

    if (MATCH_NODE_TYPE(NodeType::PRIMARYEXP, 0))
    {
        GET_NODE_PTR(PrimaryExp, primaryExp, 0)
        analyzePrimaryExp(primaryExp, buffer);
        COPY_EXP_NODE(primaryExp, root)
    }
    else if (MATCH_NODE_TYPE(NodeType::TERMINAL, 0))
    {
        GET_NODE_PTR(Term, funcName, 0)
        analyzeTerm(funcName);
        auto fParams = symbol_table.functions[funcName->v]->ParameterList;
        auto returnType = symbol_table.functions[funcName->v]->returnType;

        vector<Operand> args;
        if (root->children.size() > 3)
        {
            GET_NODE_PTR(FuncRParams, funcRParams, 2)
            analyzeFuncRParams(funcRParams, buffer, fParams, args);
        }

        if (returnType == Type::null)
        {
            buffer.push_back(new ir::CallInst(funcName->v, args, {}));
            root->t = Type::null;
        }
        else
        {
            Operand tmpVarReturn = Operand({getTmp(), returnType});
            buffer.push_back(new ir::CallInst(funcName->v, args, tmpVarReturn));
            root->v = tmpVarReturn.name;
            root->t = returnType;
        }
    }
    else if (MATCH_NODE_TYPE(NodeType::UNARYOP, 0))
    {
        GET_NODE_PTR(UnaryOp, unaryOp, 0)
        analyzeUnaryOp(unaryOp);
        GET_NODE_PTR(UnaryExp, unaryExp, 1)
        analyzeUnaryExp(unaryExp, buffer);

        if (unaryOp->op == TokenType::PLUS)
        {
            COPY_EXP_NODE(unaryExp, root)
        }
        else if (unaryOp->op == TokenType::MINU)
        {
            if (unaryExp->t == Type::IntLiteral || unaryExp->t == Type::FloatLiteral)
            {
                unaryExp->v = unaryExp->t == Type::IntLiteral ? TOS(-std::stoi(unaryExp->v)) : TOS(-std::stof(unaryExp->v));
                COPY_EXP_NODE(unaryExp, root)
            }
            else
            {
                Operand tmpVar = Operand(unaryExp->v, unaryExp->t);
                if (unaryExp->t == Type::Int)
                {
                    Operand des = Operand(getTmp(), Type::Int);
                    buffer.push_back(new Instruction({"0", Type::IntLiteral}, {tmpVar}, {des}, {Operator::sub}));
                    root->v = des.name;
                    root->t = des.type;
                }
                else
                {
                    Operand des = Operand(getTmp(), Type::Float);
                    buffer.push_back(new Instruction({"0.0", Type::FloatLiteral}, {tmpVar}, {des}, {Operator::fsub}));
                    root->v = des.name;
                    root->t = des.type;
                }
            }
        }
        else if (unaryOp->op == TokenType::NOT)
        {
            if (unaryExp->t == Type::IntLiteral || unaryExp->t == Type::FloatLiteral)
            {
                unaryExp->v = unaryExp->t == Type::IntLiteral ? TOS(!std::stoi(unaryExp->v)) : TOS(!std::stof(unaryExp->v));
                COPY_EXP_NODE(unaryExp, root)
            }
            else
            {
                Operand tmpVar = Operand(unaryExp->v, unaryExp->t);
                if (unaryExp->t == Type::Int)
                {
                    Operand des = Operand(getTmp(), Type::Int);
                    buffer.push_back(new Instruction({"0", Type::IntLiteral}, {tmpVar}, {des}, {Operator::eq}));
                    root->v = des.name;
                    root->t = des.type;
                }
                else
                {
                    assert(0 && "to be continue");
                }
            }
        }
        else
            assert(0 && "UnaryOp type error");
    }
    else
        assert(0 && "analyzeUnaryExp error");
}

void frontend::Analyzer::analyzePrimaryExp(PrimaryExp *root, vector<ir::Instruction *> &buffer)
{

    if (root->children.size() > 1)
    {
        GET_NODE_PTR(Exp, exp, 1)
        analyzeExp(exp, buffer);
        COPY_EXP_NODE(exp, root);
    }
    else if (MATCH_NODE_TYPE(NodeType::LVAL, 0))
    {
        GET_NODE_PTR(LVal, lVal, 0)
        analyzeLVal(lVal, buffer);

        if (lVal->t == Type::IntPtr || lVal->t == Type::FloatPtr)
        {
            Operand lValVar = Operand(lVal->v, lVal->t);
            Operand offsetVar = Operand(lVal->offset, Type::Int);
            if (lVal->isPtr)
            {
                auto tmpVar = Operand(getTmp(), lVal->t);
                buffer.push_back(new Instruction({lValVar}, {offsetVar}, {tmpVar}, {Operator::getptr}));
                root->v = tmpVar.name;
                root->t = tmpVar.type;
            }
            else
            {
                if (lVal->t == Type::IntPtr)
                {
                    auto tmpVar = Operand(getTmp(), Type::Int);
                    buffer.push_back(new Instruction({lValVar}, {offsetVar}, {tmpVar}, {Operator::load}));
                    root->v = tmpVar.name;
                    root->t = tmpVar.type;
                }
                else if (lVal->t == Type::FloatPtr)
                {

                    auto tmpVar = Operand(getTmp(), Type::Float);
                    buffer.push_back(new Instruction({lValVar}, {offsetVar}, {tmpVar}, {Operator::load}));
                    root->v = tmpVar.name;
                    root->t = tmpVar.type;
                }
                else
                    assert(0 && "lVal type error");
            }
        }
        else
        {
            COPY_EXP_NODE(lVal, root)
        }
    }
    else if (MATCH_NODE_TYPE(NodeType::NUMBER, 0))
    {
        GET_NODE_PTR(Number, number, 0)
        analyzeNumber(number, buffer);
        COPY_EXP_NODE(number, root)
    }
    else
        assert(0 && "analyzePrimaryExp error");
}

void frontend::Analyzer::analyzeNumber(Number *root, vector<ir::Instruction *> &buffer)
{

    GET_NODE_PTR(Term, term, 0)
    if (term->token.type == TokenType::INTLTR)
    {
        root->t = Type::IntLiteral;

        const string &tokenVal = term->token.value;
        if (tokenVal.length() >= 3 && tokenVal[0] == '0' && (tokenVal[1] == 'x' || tokenVal[1] == 'X'))
            root->v = std::to_string(std::stoi(tokenVal, nullptr, 16));
        else if (tokenVal.length() >= 3 && tokenVal[0] == '0' && (tokenVal[1] == 'b' || tokenVal[1] == 'B'))
            root->v = std::to_string(std::stoi(tokenVal.substr(2), nullptr, 2));
        else if (tokenVal.length() >= 2 && tokenVal[0] == '0')
            root->v = std::to_string(std::stoi(tokenVal, nullptr, 8));
        else
            root->v = tokenVal;
    }
    else if (term->token.type == TokenType::FLOATLTR)
    {
        root->t = Type::FloatLiteral;
        root->v = term->token.value;
    }
    else
        assert(0 && "analyzeNumber error");
}

void frontend::Analyzer::analyzeVarDecl(VarDecl *root, vector<ir::Instruction *> &buffer)
{

    GET_NODE_PTR(BType, bType, 0)
    analyzeBType(bType);
    root->t = bType->t;
    for (int i = 1; i < root->children.size(); i += 2)
    {
        GET_NODE_PTR(VarDef, varDef, i)
        analyzeVarDef(varDef, buffer, root->t);
    }
}

void frontend::Analyzer::analyzeBType(BType *root)
{

    GET_NODE_PTR(Term, term, 0)
    if (term->token.type == TokenType::INTTK)
        root->t = Type::Int;
    else if (term->token.type == TokenType::FLOATTK)
        root->t = Type::Float;
    else
        assert(0 && "analyzeBType error");
}

void frontend::Analyzer::analyzeVarDef(VarDef *root, vector<ir::Instruction *> &buffer, ir::Type type)
{

    GET_NODE_PTR(Term, term, 0)
    analyzeTerm(term);
    root->arr_name = symbol_table.get_scoped_name(term->v);

    vector<int> dimension;
    int size;

    if (root->children.size() > 1 && MATCH_NODE_TYPE(NodeType::CONSTEXP, 2))
    {
        size = 1;

        for (int i = 2; i < root->children.size(); i += 3)
        {
            if (MATCH_NODE_TYPE(NodeType::CONSTEXP, i))
            {
                GET_NODE_PTR(ConstExp, constExp, i)
                analyzeConstExp(constExp);
                assert(constExp->t == Type::IntLiteral && std::stoi(constExp->v) >= 0);
                dimension.push_back(std::stoi(constExp->v));
                size *= std::stoi(constExp->v);
            }
            else
                break;
        }
    }
    else
        size = 0;

    if (MATCH_NODE_TYPE(NodeType::INITVAL, root->children.size() - 1))
    {
        GET_NODE_PTR(InitVal, initVal, root->children.size() - 1)
        initVal->v = root->arr_name;
        if (type == Type::Int)
        {
            initVal->t = Type::Int;
            if (size == 0)
            {
                symbol_table.scope_stack.back().table[term->token.value] = STE(Operand(root->arr_name, Type::Int), dimension, size);
            }
            else
            {
                symbol_table.scope_stack.back().table[term->token.value] = STE(Operand(root->arr_name, Type::IntPtr), dimension, size);

                buffer.push_back(new Instruction({TOS(size), Type::IntLiteral}, {}, {root->arr_name, Type::IntPtr}, {Operator::alloc}));
            }
        }
        else if (type == Type::Float)
        {
            initVal->t = Type::Float;
            if (size == 0)
            {
                symbol_table.scope_stack.back().table[term->token.value] = STE(Operand(root->arr_name, Type::Float), dimension, size);
            }
            else
            {
                symbol_table.scope_stack.back().table[term->token.value] = STE(Operand(root->arr_name, Type::FloatPtr), dimension, size);

                buffer.push_back(new Instruction({TOS(size), Type::IntLiteral}, {}, {root->arr_name, Type::FloatPtr}, {Operator::alloc}));
            }
        }
        else
            assert(0 && "InitVal type error");

        analyzeInitVal(initVal, buffer, size, 0, 0, dimension);
    }
    else
    {

        if (type == Type::Int)
        {
            if (size == 0)
            {
                symbol_table.scope_stack.back().table[term->token.value] = STE(Operand(root->arr_name, Type::Int), dimension, size);

                if (symbol_table.scope_stack.size() > 1)
                    buffer.push_back(new Instruction({"473289", Type::IntLiteral}, {}, {root->arr_name, Type::Int}, {Operator::def}));
            }
            else
            {
                symbol_table.scope_stack.back().table[term->token.value] = STE(Operand(root->arr_name, Type::IntPtr), dimension, size);
                if (symbol_table.scope_stack.size() > 1)
                    buffer.push_back(new Instruction({TOS(size), Type::IntLiteral}, {}, {root->arr_name, Type::IntPtr}, {Operator::alloc}));
            }
        }
        else if (type == Type::Float)
        {
            if (size == 0)
            {
                symbol_table.scope_stack.back().table[term->token.value] = STE(Operand(root->arr_name, Type::Float), dimension, size);

                if (symbol_table.scope_stack.size() > 1)
                    buffer.push_back(new Instruction({"3.1415926", Type::FloatLiteral}, {}, {root->arr_name, Type::Float}, {Operator::fdef}));
            }
            else
            {
                symbol_table.scope_stack.back().table[term->token.value] = STE(Operand(root->arr_name, Type::FloatPtr), dimension, size);
                if (symbol_table.scope_stack.size() > 1)
                    buffer.push_back(new Instruction({TOS(size), Type::IntLiteral}, {}, {root->arr_name, Type::FloatPtr}, {Operator::alloc}));
            }
        }
        else
            assert(0 && "InitVal type error");
    }
}

void frontend::Analyzer::analyzeConstExp(ConstExp *root)
{

    GET_NODE_PTR(AddExp, addExp, 0)
    vector<Instruction *> tmpInst;
    analyzeAddExp(addExp, tmpInst);
    COPY_EXP_NODE(addExp, root)
}

void frontend::Analyzer::analyzeInitVal(InitVal *root, vector<ir::Instruction *> &buffer, int size, int cur, int offset, vector<int> &dimension)
{

    if (MATCH_NODE_TYPE(NodeType::EXP, 0) && size == 0)
    {

        GET_NODE_PTR(Exp, exp, 0)
        analyzeExp(exp, buffer);

        if (root->t == Type::Int && exp->t == Type::IntLiteral)
        {
            if (symbol_table.scope_stack.size() > 1)
            {
                buffer.push_back(new Instruction({exp->v, exp->t}, {}, {root->v, Type::Int}, {Operator::def}));
            }
            else
            {
                auto tmpVar = IntLiteral2Int(exp->v, buffer);
                buffer.push_back(new Instruction(tmpVar, {}, Operand(root->v, Type::Int), Operator::mov));
            }
        }
        else if (root->t == Type::Float && exp->t == Type::FloatLiteral)
        {

            if (symbol_table.scope_stack.size() > 1)
            {
                buffer.push_back(new Instruction({exp->v, exp->t}, {}, {root->v, Type::Float}, {Operator::fdef}));
            }
            else
            {
                assert(0 && "to be continue");
            }
        }
        else if (root->t == Type::Int && exp->t == Type::Int)
        {
            Operand tmpVar = Operand(exp->v, exp->t);
            buffer.push_back(new Instruction({tmpVar}, {}, {root->v, Type::Int}, {Operator::mov}));
        }
        else if (root->t == Type::Float && exp->t == Type::Float)
        {

            Operand tmpVar = Operand(exp->v, exp->t);
            buffer.push_back(new Instruction({tmpVar}, {}, {root->v, Type::Float}, {Operator::fmov}));
        }
        else
        {
            assert(0 && "to be continue");
        }
    }
    else if (MATCH_NODE_TYPE(NodeType::TERMINAL, 0))
    {
        assert(size >= 1);
        size /= dimension[cur];
        int cnt = 0, tot = root->children.size() / 2;
        for (int i = 1; i < root->children.size() - 1; i += 2)
        {
            GET_NODE_PTR(InitVal, initVal, i)
            COPY_EXP_NODE(root, initVal)
            if (tot <= dimension[cur])
            {
                analyzeInitVal(initVal, buffer, size, cur + 1, offset + cnt * size, dimension);
            }
            else
            {
                analyzeInitVal(initVal, buffer, 1, cur, offset + cnt, dimension);
            }
            cnt++;
        }

        for (int i = cnt * size; i < dimension[cur] * size; i++)
        {
            Type type = (root->t == Type::Int) ? Type::IntLiteral : Type::FloatLiteral;
            Operand tmpVar = (type == Type::IntLiteral) ? IntLiteral2Int("0", buffer) : FloatLiteral2Float("0.0", buffer);
            buffer.push_back(new Instruction({root->v, (root->t == Type::Int ? Type::IntPtr : Type::FloatPtr)}, {TOS(i), Type::IntLiteral}, {tmpVar}, {Operator::store}));
        }
    }
    else if (dynamic_cast<InitVal *>(root->parent))
    {
        GET_NODE_PTR(Exp, exp, 0);
        analyzeExp(exp, buffer);

        if (root->t == Type::Int && exp->t == Type::IntLiteral)
        {
            buffer.push_back(new Instruction({root->v, Type::IntPtr}, {TOS(offset), Type::IntLiteral}, {exp->v, exp->t}, {Operator::store}));

        }
        else if (root->t == Type::Float && exp->t == Type::FloatLiteral)
        {
            Operand expVar = FloatLiteral2Float(exp->v, buffer);
            buffer.push_back(new Instruction({root->v, Type::FloatPtr}, {TOS(offset), Type::IntLiteral}, {expVar}, {Operator::store}));
        }
        else if (root->t == Type::Float && exp->t == Type::IntLiteral)
        {
            exp->v = TOS(float(std::stoi(exp->v)));
            exp->t = Type ::FloatLiteral;
            Operand expVar = FloatLiteral2Float(exp->v, buffer);
            buffer.push_back(new Instruction({root->v, Type::FloatPtr}, {TOS(offset), Type::IntLiteral}, {expVar}, {Operator::store}));
        }
        else
        {
            assert(0 && "to be continue");
        }
    }
    else
        assert(0 && "analyzeInitVal error");
}

void frontend::Analyzer::analyzeLVal(LVal *root, vector<ir::Instruction *> &buffer)
{

    GET_NODE_PTR(Term, valName, 0);
    analyzeTerm(valName);
    auto ste = symbol_table.get_ste(valName->v);

    if (ste.isConst && (ste.operand.type == Type::Int || ste.operand.type == Type::Float))
    {
        root->v = ste.val;
        root->t = (ste.operand.type == Type::Int) ? Type::IntLiteral : Type::FloatLiteral;
        root->isPtr = false;
    }
    else
    {
        root->v = ste.operand.name;
        root->t = ste.operand.type;

        if (ste.size == 0)
        {
            root->isPtr = false;
        }
        else
        {
            int cur = 0, curSize = ste.size;
            Operand offsetVar = IntLiteral2Int("0", buffer);
            for (int i = 2; i < root->children.size(); i += 3)
            {
                curSize /= ste.dimension[cur++];
                Operand tmpVar = IntLiteral2Int(TOS(curSize), buffer);
                GET_NODE_PTR(Exp, exp, i)
                analyzeExp(exp, buffer);
                auto expVar = exp->t == Type::IntLiteral ? IntLiteral2Int(exp->v, buffer) : Operand(exp->v, exp->t);
                buffer.push_back(new Instruction({tmpVar}, {expVar}, {tmpVar}, {Operator::mul}));
                buffer.push_back(new Instruction({offsetVar}, {tmpVar}, {offsetVar}, {Operator::add}));
            }
            root->offset = offsetVar.name;
            root->isPtr = cur < ste.dimension.size();
        }
    }
}

void frontend::Analyzer::analyzeConstDecl(ConstDecl *root, vector<ir::Instruction *> &buffer)
{

    GET_NODE_PTR(BType, bType, 1)
    analyzeBType(bType);
    root->t = bType->t;
    for (int i = 2; i < root->children.size(); i += 2)
    {
        GET_NODE_PTR(ConstDef, constDef, i)
        analyzeConstDef(constDef, buffer, root->t);
    }
}

void frontend::Analyzer::analyzeConstDef(ConstDef *root, vector<ir::Instruction *> &buffer, ir::Type type)
{

    GET_NODE_PTR(Term, term, 0)
    analyzeTerm(term);
    root->arr_name = symbol_table.get_scoped_name(term->v);

    vector<int> dimension;
    int size;
    if (root->children.size() > 1 && MATCH_NODE_TYPE(NodeType::CONSTEXP, 2))
    {
        size = 1;

        for (int i = 2; i < root->children.size(); i += 3)
        {
            if (MATCH_NODE_TYPE(NodeType::CONSTEXP, i))
            {
                GET_NODE_PTR(ConstExp, constExp, i)
                analyzeConstExp(constExp);
                assert(constExp->t == Type::IntLiteral && std::stoi(constExp->v) >= 0);
                dimension.push_back(std::stoi(constExp->v));
                size *= std::stoi(constExp->v);
            }
            else
                break;
        }
    }
    else
        size = 0;

    GET_NODE_PTR(ConstInitVal, constInitVal, root->children.size() - 1)
    constInitVal->v = term->token.value;
    if (type == Type::Int)
    {
        if (size == 0)
        {
            symbol_table.scope_stack.back().table[term->token.value] = STE(Operand(root->arr_name, Type::Int), dimension, size, true);
            constInitVal->t = Type::Int;
        }
        else
        {
            symbol_table.scope_stack.back().table[term->token.value] = STE(Operand(root->arr_name, Type::IntPtr), dimension, size, true);
            constInitVal->t = Type::IntLiteral;

            buffer.push_back(new Instruction({TOS(size), Type::IntLiteral}, {}, {root->arr_name, Type::IntPtr}, {Operator::alloc}));

        }
    }
    else if (type == Type::Float)
    {
        if (size == 0)
        {
            symbol_table.scope_stack.back().table[term->token.value] = STE(Operand(root->arr_name, Type::Float), dimension, size, true);
            constInitVal->t = Type::Float;
        }
        else
        {
            assert(0 && "to be continue");
        }
    }
    else
        assert(0 && "analyzeConstDef error");
    analyzeConstInitVal(constInitVal, buffer, size, 0, 0, dimension);
}

void frontend::Analyzer::analyzeConstInitVal(ConstInitVal *root, vector<ir::Instruction *> &buffer, int size, int cur, int offset, vector<int> &dimension)
{

    if (size == 0)
    {
        GET_NODE_PTR(ConstExp, constExp, 0)
        analyzeConstExp(constExp);

        if (root->t == Type::Int)
        {
            if (constExp->t == Type::IntLiteral)
            {
                symbol_table.scope_stack.back().table[root->v].val = constExp->v;
            }
            else if (constExp->t == Type::FloatLiteral)
            {

                constExp->v = TOS(int(stof(constExp->v)));
                constExp->t = Type::IntLiteral;
                symbol_table.scope_stack.back().table[root->v].val = constExp->v;
            }
            else
                assert(0 && "ConstInitVal type error");
        }
        else if (root->t == Type::Float)
        {
            if (constExp->t == Type::FloatLiteral)
            {
                symbol_table.scope_stack.back().table[root->v].val = constExp->v;
            }
            else if (constExp->t == Type::IntLiteral)
            {

                constExp->v = TOS(float(stoi(constExp->v)));
                constExp->t = Type::FloatLiteral;
                symbol_table.scope_stack.back().table[root->v].val = constExp->v;
            }
            else
                assert(0 && "ConstInitVal type error");
        }
    }
    else
    {
        if (MATCH_NODE_TYPE(NodeType::TERMINAL, 0))
        {
            assert(size >= 1);
            size /= dimension[cur];
            int cnt = 0, tot = root->children.size() / 2;
            for (int i = 1; i < root->children.size() - 1; i += 2)
            {
                GET_NODE_PTR(ConstInitVal, constInitVal, i)
                COPY_EXP_NODE(root, constInitVal)
                if (tot <= dimension[cur])
                {
                    analyzeConstInitVal(constInitVal, buffer, size, cur + 1, offset + cnt * size, dimension);
                }
                else
                {
                    analyzeConstInitVal(constInitVal, buffer, 1, cur, offset + cnt, dimension);
                }
                cnt++;
            }

            for (int i = cnt * size; i < dimension[cur] * size; i++)
            {
                Type type = (root->t == Type::Int) ? Type::IntLiteral : Type::FloatLiteral;
                Operand tmpVar = (type == Type::IntLiteral) ? IntLiteral2Int("0", buffer) : FloatLiteral2Float("0.0", buffer);

                buffer.push_back(new Instruction({symbol_table.get_scoped_name(root->v), (root->t == Type::Int ? Type::IntPtr : Type::FloatLiteral)}, {TOS(i), Type::IntLiteral}, {tmpVar}, {Operator::store}));
            }
        }
        else if (dynamic_cast<ConstInitVal *>(root->parent))
        {
            GET_NODE_PTR(ConstExp, constExp, 0);
            analyzeConstExp(constExp);

            if (root->t == Type::IntLiteral && constExp->t == Type::IntLiteral)
            {
                buffer.push_back(new Instruction({symbol_table.get_scoped_name(root->v), Type::IntPtr}, {TOS(offset), Type::IntLiteral}, {constExp->v, constExp->t}, {Operator::store}));
            }
            else
            {
                assert(0 && "to be continue");
            }
        }
        else
            assert(0 && "analyzeConstInitVal error");
    }
}

void frontend::Analyzer::analyzeFuncRParams(FuncRParams *root, vector<ir::Instruction *> &buffer, vector<ir::Operand> &fParams, vector<ir::Operand> &args)
{

    for (int i = 0, curParam = 0; i < root->children.size(); i += 2)
    {
        GET_NODE_PTR(Exp, exp, i)
        analyzeExp(exp, buffer);
        Operand fParam = fParams[curParam++];
        Operand arg = Operand(exp->v, exp->t);
        if (fParam.type == Type::Int)
        {
            if (arg.type == Type::Int || arg.type == Type::IntLiteral)
            {
                args.push_back(arg);
            }
            else if (arg.type == Type::FloatLiteral)
            {

                arg.name = TOS(int(std::stof(arg.name)));
                arg.type = Type::IntLiteral;
                args.push_back(arg);
            }
            else if (arg.type == Type::Float)
            {

                Operand tmpVar = Operand(getTmp(), Type::Int);
                buffer.push_back(new Instruction({arg}, {}, {tmpVar}, {Operator::cvt_f2i}));
                std::swap(arg, tmpVar);
                args.push_back(arg);
            }
            else
            {
                assert(0 && "to be continue");
            }
        }
        else if (fParam.type == Type::Float)
        {

            if (arg.type == Type::Float || arg.type == Type::FloatLiteral)
            {
                args.push_back(arg);
            }
            else
            {
                assert(0 && "to be continue");
            }
        }
        else if (fParam.type == Type::IntPtr || fParam.type == Type::FloatPtr)
        {

            args.push_back(arg);
        }
        else
        {
            assert(0 && "to be continue");
        }
    }
}

void frontend::Analyzer::analyzeCond(Cond *root, vector<ir::Instruction *> &buffer)
{

    GET_NODE_PTR(LOrExp, lOrExp, 0)
    analyzeLOrExp(lOrExp, buffer);
    COPY_EXP_NODE(lOrExp, root)
}

void frontend::Analyzer::analyzeLOrExp(LOrExp *root, vector<ir::Instruction *> &buffer)
{

    GET_NODE_PTR(LAndExp, lAndExp, 0)
    vector<Instruction *> lAndExpInst;
    analyzeLAndExp(lAndExp, lAndExpInst);

    if (root->children.size() == 1)
    {
        buffer.insert(buffer.end(), lAndExpInst.begin(), lAndExpInst.end());
        COPY_EXP_NODE(lAndExp, root);
    }
    else
    {
        GET_NODE_PTR(LOrExp, lOrExp, 2)
        vector<Instruction *> lOrExpInst;
        analyzeLOrExp(lOrExp, lOrExpInst);

        if ((lAndExp->t == Type::IntLiteral || lAndExp->t == Type::FloatLiteral) && (lOrExp->t == Type::IntLiteral || lOrExp->t == Type::FloatLiteral))
        {
            root->t = Type::IntLiteral;
            if (lAndExp->t == Type::IntLiteral && lOrExp->t == Type::IntLiteral)
            {
                root->v = TOS(std::stoi(lAndExp->v) || std::stoi(lOrExp->v));
            }
            else if (lAndExp->t == Type::IntLiteral && lOrExp->t == Type::FloatLiteral)
            {

                root->v = TOS(std::stoi(lAndExp->v) || std::stof(lOrExp->v));
            }
            else
            {
                assert(0 && "to be continue");
            }
        }
        else
        {

            if (lAndExp->t == Type::IntLiteral || lAndExp->t == Type::FloatLiteral)
            {
                if ((lAndExp->t == Type::IntLiteral && stoi(lAndExp->v) != 0) || (lAndExp->t == Type::Float && stof(lAndExp->v) != 0))
                {
                    root->v = "1";
                    root->t = Type::IntLiteral;
                }
                else
                {
                    buffer.insert(buffer.end(), lOrExpInst.begin(), lOrExpInst.end());
                    COPY_EXP_NODE(lOrExp, root)
                }
            }
            else
            {
                Operand op1 = Operand(lAndExp->v, lAndExp->t);
                Operand op2;
                if (lOrExp->t == Type::IntLiteral)
                {
                    op2 = IntLiteral2Int(lOrExp->v, buffer);
                }
                else if (lOrExp->t == Type::FloatLiteral)
                {
                    op2 = FloatLiteral2Float(lOrExp->v, buffer);
                }
                else
                {
                    op2 = Operand(lOrExp->v, lOrExp->t);
                }
                Operand des = Operand(getTmp(), Type::Int);
                buffer.insert(buffer.end(), lAndExpInst.begin(), lAndExpInst.end());

                buffer.push_back(new Instruction({op1}, {}, {des}, {Operator::mov}));

                buffer.push_back(new Instruction({des}, {}, {TOS(lOrExpInst.size() + 2), Type::IntLiteral}, {Operator::_goto}));
                buffer.insert(buffer.end(), lOrExpInst.begin(), lOrExpInst.end());
                buffer.push_back(new Instruction({des}, {op2}, {des}, {Operator::_or}));
                root->v = des.name;
                root->t = des.type;
            }
        }
    }
}

void frontend::Analyzer::analyzeLAndExp(LAndExp *root, vector<ir::Instruction *> &buffer)
{

    GET_NODE_PTR(EqExp, eqExp, 0)
    vector<Instruction *> eqExpInst;
    analyzeEqExp(eqExp, eqExpInst);

    if (root->children.size() == 1)
    {
        buffer.insert(buffer.end(), eqExpInst.begin(), eqExpInst.end());
        COPY_EXP_NODE(eqExp, root);
    }
    else
    {
        GET_NODE_PTR(LAndExp, lAndExp, 2)
        vector<Instruction *> lAndExpInst;
        analyzeLAndExp(lAndExp, lAndExpInst);

        if ((eqExp->t == Type::IntLiteral || eqExp->t == Type::FloatLiteral) && (lAndExp->t == Type::IntLiteral || lAndExp->t == Type::FloatLiteral))
        {
            root->t = Type::IntLiteral;
            if (eqExp->t == Type::IntLiteral && lAndExp->t == Type::IntLiteral)
            {
                assert(0 && "to be continue");

            }
            else if (eqExp->t == Type::FloatLiteral && lAndExp->t == Type::FloatLiteral)
            {

                root->v = TOS(std::stof(eqExp->v) && std::stof(lAndExp->v));
            }
            else
            {
                assert(0 && "to be continue");
            }
        }
        else
        {

            if (eqExp->t == Type::IntLiteral || eqExp->t == Type::FloatLiteral)
            {
                if ((eqExp->t == Type::IntLiteral && stoi(eqExp->v) == 0) || (eqExp->t == Type::Float && stof(eqExp->v) == 0))
                {
                    root->v = "0";
                    root->t = Type::IntLiteral;
                }
                else
                {
                    buffer.insert(buffer.end(), lAndExpInst.begin(), lAndExpInst.end());
                    COPY_EXP_NODE(lAndExp, root)
                }
            }
            else
            {
                Operand op1 = Operand(eqExp->v, eqExp->t);
                Operand op2;
                if (lAndExp->t == Type::IntLiteral)
                {
                    op2 = IntLiteral2Int(lAndExp->v, buffer);
                }
                else if (lAndExp->t == Type::FloatLiteral)
                {
                    op2 = FloatLiteral2Float(lAndExp->v, buffer);
                }
                else
                {
                    op2 = Operand(lAndExp->v, lAndExp->t);
                }
                Operand des = Operand(getTmp(), Type::Int);
                buffer.insert(buffer.end(), eqExpInst.begin(), eqExpInst.end());

                Operand tmpVar = Operand(getTmp(), Type::Int);
                buffer.push_back(new Instruction({op1}, {}, {des}, {Operator::mov}));
                buffer.push_back(new Instruction({des}, {"0", Type::IntLiteral}, {tmpVar}, {Operator::eq}));
                buffer.push_back(new Instruction({tmpVar}, {}, {TOS(lAndExpInst.size() + 2), Type::IntLiteral}, {Operator::_goto}));
                buffer.insert(buffer.end(), lAndExpInst.begin(), lAndExpInst.end());
                buffer.push_back(new Instruction({des}, {op2}, {des}, {Operator::_and}));
                root->v = des.name;
                root->t = des.type;
            }
        }
    }
}

void frontend::Analyzer::analyzeEqExp(EqExp *root, vector<ir::Instruction *> &buffer)
{

    GET_NODE_PTR(RelExp, relExp1, 0)
    analyzeRelExp(relExp1, buffer);

    int idx = -1;

    if (relExp1->t == Type::IntLiteral || relExp1->t == Type::FloatLiteral)
    {
        for (int i = 2; i < root->children.size(); i += 2)
        {
            vector<Instruction *> relExpInst;
            GET_NODE_PTR(Term, term, i - 1)
            GET_NODE_PTR(RelExp, relExp2, i)
            analyzeRelExp(relExp2, relExpInst);
            if (relExp2->t == Type::IntLiteral || relExp2->t == Type::FloatLiteral)
            {
                if (relExp1->t == Type::IntLiteral && relExp2->t == Type::IntLiteral)
                {
                    if (term->token.type == TokenType::EQL)
                    {
                        relExp1->v = TOS(std::stoi(relExp1->v) == std::stoi(relExp2->v));
                    }
                    else if (term->token.type == TokenType::NEQ)
                    {
                        relExp1->v = TOS(std::stoi(relExp1->v) != std::stoi(relExp2->v));
                    }
                    else
                        assert(0 && "EqExp op error");
                }
                else if (relExp1->t == Type::IntLiteral && relExp2->t == Type::FloatLiteral)
                {
                    relExp1->t = Type::FloatLiteral;
                    if (term->token.type == TokenType::EQL)
                    {
                        relExp1->v = TOS(std::stoi(relExp1->v) == std::stof(relExp2->v));
                    }
                    else if (term->token.type == TokenType::NEQ)
                    {
                        relExp1->v = TOS(std::stoi(relExp1->v) != std::stof(relExp2->v));
                    }
                    else
                        assert(0 && "EqExp op error");
                }
                else if (relExp1->t == Type::FloatLiteral && relExp2->t == Type::IntLiteral)
                {
                    if (term->token.type == TokenType::EQL)
                    {
                        relExp1->v = TOS(std::stof(relExp1->v) == std::stoi(relExp2->v));
                    }
                    else if (term->token.type == TokenType::NEQ)
                    {
                        relExp1->v = TOS(std::stof(relExp1->v) != std::stoi(relExp2->v));
                    }
                    else
                        assert(0 && "EqExp op error");
                }
                else
                {
                    if (term->token.type == TokenType::EQL)
                    {
                        relExp1->v = TOS(std::stof(relExp1->v) == std::stof(relExp2->v));
                    }
                    else if (term->token.type == TokenType::NEQ)
                    {
                        relExp1->v = TOS(std::stof(relExp1->v) != std::stof(relExp2->v));
                    }
                    else
                        assert(0 && "EqExp op error");
                }
            }
            else
            {
                idx = i;
                break;
            }
        }
    }

    if ((relExp1->t == Type::IntLiteral || relExp1->t == Type::FloatLiteral) && idx == -1)
    {
        COPY_EXP_NODE(relExp1, root)
    }
    else
    {

        Operand op1;
        if (idx == -1)
        {
            op1.name = relExp1->v;
            op1.type = relExp1->t;
            idx = 2;
        }
        else
        {
            if (relExp1->t == Type::IntLiteral)
            {
                op1 = IntLiteral2Int(relExp1->v, buffer);
            }
            else
            {
                op1 = FloatLiteral2Float(relExp1->v, buffer);
            }
        }

        if (root->children.size() > 1)
        {
            if ((op1.type == Type::Int || op1.type == Type::Float))
            {
                auto tmpVar = Operand(getTmp(), op1.type == Type::Int ? Type::Int : Type::Float);
                Operator instType = (op1.type == Type::Int) ? Operator::mov : Operator::fmov;
                buffer.push_back(new Instruction(op1, {}, tmpVar, instType));
                std::swap(op1, tmpVar);
            }

            for (int i = idx; i < root->children.size(); i += 2)
            {
                GET_NODE_PTR(Term, term, i - 1)
                GET_NODE_PTR(RelExp, relExp2, i)
                analyzeRelExp(relExp2, buffer);

                Operand op2;
                if (relExp2->t == Type::IntLiteral)
                {
                    op2 = IntLiteral2Int(relExp2->v, buffer);
                }
                else if (relExp2->t == Type::FloatLiteral)
                {
                    op2 = FloatLiteral2Float(relExp2->v, buffer);
                }
                else
                {
                    op2 = Operand(relExp2->v, relExp2->t);
                }

                if (term->token.type == TokenType::EQL)
                {
                    if (op1.type == Type::Int && op2.type == Type::Int)
                    {
                        buffer.push_back(new Instruction(op1, op2, op1, Operator::eq));
                    }
                    else
                    {
                        assert(0 && "to be continue");
                    }
                }
                else if (term->token.type == TokenType::NEQ)
                {
                    if (op1.type == Type::Int && op2.type == Type::Int)
                    {
                        buffer.push_back(new Instruction(op1, op2, op1, Operator::neq));
                    }
                    else
                    {
                        assert(0 && "to be continue");
                    }
                }
                else
                    assert(0 && "EqExp op error");
            }
        }

        root->t = op1.type;
        root->v = op1.name;
    }
}

void frontend::Analyzer::analyzeRelExp(RelExp *root, vector<ir::Instruction *> &buffer)
{

    GET_NODE_PTR(AddExp, addExp1, 0)
    analyzeAddExp(addExp1, buffer);

    int idx = -1;

    if (addExp1->t == Type::IntLiteral || addExp1->t == Type::FloatLiteral)
    {
        for (int i = 2; i < root->children.size(); i += 2)
        {
            vector<Instruction *> addExpInst;
            GET_NODE_PTR(Term, term, i - 1)
            GET_NODE_PTR(AddExp, addExp2, i)
            analyzeAddExp(addExp2, addExpInst);
            if (addExp2->t == Type::IntLiteral || addExp2->t == Type::FloatLiteral)
            {
                if (addExp1->t == Type::IntLiteral && addExp2->t == Type::IntLiteral)
                {
                    if (term->token.type == TokenType::LSS)
                    {
                        addExp1->v = TOS(std::stoi(addExp1->v) < std::stoi(addExp2->v));
                    }
                    else if (term->token.type == TokenType::GTR)
                    {
                        addExp1->v = TOS(std::stoi(addExp1->v) > std::stoi(addExp2->v));
                    }
                    else if (term->token.type == TokenType::LEQ)
                    {
                        addExp1->v = TOS(std::stoi(addExp1->v) <= std::stoi(addExp2->v));
                    }
                    else if (term->token.type == TokenType::GEQ)
                    {
                        addExp1->v = TOS(std::stoi(addExp1->v) >= std::stoi(addExp2->v));
                    }
                    else
                        assert(0 && "RelExp op error");
                }
                else if (addExp1->t == Type::IntLiteral && addExp2->t == Type::FloatLiteral)
                {
                    addExp1->t = Type::FloatLiteral;
                    if (term->token.type == TokenType::LSS)
                    {
                        addExp1->v = TOS(std::stoi(addExp1->v) < std::stof(addExp2->v));
                    }
                    else if (term->token.type == TokenType::GTR)
                    {
                        addExp1->v = TOS(std::stoi(addExp1->v) > std::stof(addExp2->v));
                    }
                    else if (term->token.type == TokenType::LEQ)
                    {
                        addExp1->v = TOS(std::stoi(addExp1->v) <= std::stof(addExp2->v));
                    }
                    else if (term->token.type == TokenType::GEQ)
                    {
                        addExp1->v = TOS(std::stoi(addExp1->v) >= std::stof(addExp2->v));
                    }
                    else
                        assert(0 && "RelExp op error");
                }
                else if (addExp1->t == Type::FloatLiteral && addExp2->t == Type::IntLiteral)
                {
                    if (term->token.type == TokenType::LSS)
                    {
                        addExp1->v = TOS(std::stof(addExp1->v) < std::stoi(addExp2->v));
                    }
                    else if (term->token.type == TokenType::GTR)
                    {
                        addExp1->v = TOS(std::stof(addExp1->v) > std::stoi(addExp2->v));
                    }
                    else if (term->token.type == TokenType::LEQ)
                    {
                        addExp1->v = TOS(std::stof(addExp1->v) <= std::stoi(addExp2->v));
                    }
                    else if (term->token.type == TokenType::GEQ)
                    {
                        addExp1->v = TOS(std::stof(addExp1->v) >= std::stoi(addExp2->v));
                    }
                    else
                        assert(0 && "RelExp op error");
                }
                else
                {
                    if (term->token.type == TokenType::LSS)
                    {
                        addExp1->v = TOS(std::stof(addExp1->v) < std::stof(addExp2->v));
                    }
                    else if (term->token.type == TokenType::GTR)
                    {
                        addExp1->v = TOS(std::stof(addExp1->v) > std::stof(addExp2->v));
                    }
                    else if (term->token.type == TokenType::LEQ)
                    {
                        addExp1->v = TOS(std::stof(addExp1->v) <= std::stof(addExp2->v));
                    }
                    else if (term->token.type == TokenType::GEQ)
                    {
                        addExp1->v = TOS(std::stof(addExp1->v) >= std::stof(addExp2->v));
                    }
                    else
                        assert(0 && "RelExp op error");
                }
            }
            else
            {
                idx = i;
                break;
            }
        }
    }

    if ((addExp1->t == Type::IntLiteral || addExp1->t == Type::FloatLiteral) && idx == -1)
    {
        COPY_EXP_NODE(addExp1, root)
    }
    else
    {

        Operand op1;
        if (idx == -1)
        {
            op1.name = addExp1->v;
            op1.type = addExp1->t;
            idx = 2;
        }
        else
        {
            if (addExp1->t == Type::IntLiteral)
            {
                op1 = IntLiteral2Int(addExp1->v, buffer);
            }
            else
            {
                op1 = FloatLiteral2Float(addExp1->v, buffer);
            }
        }

        if (root->children.size() > 1)
        {
            if ((op1.type == Type::Int || op1.type == Type::Float))
            {
                auto tmpVar = Operand(getTmp(), op1.type == Type::Int ? Type::Int : Type::Float);
                Operator instType = (op1.type == Type::Int) ? Operator::mov : Operator::fmov;
                buffer.push_back(new Instruction(op1, {}, tmpVar, instType));
                std::swap(op1, tmpVar);
            }
            else
                assert(0 && "op1 type error");

            for (int i = idx; i < root->children.size(); i += 2)
            {
                GET_NODE_PTR(Term, term, i - 1)
                GET_NODE_PTR(AddExp, addExp2, i)
                analyzeAddExp(addExp2, buffer);

                Operand op2;
                if (addExp2->t == Type::IntLiteral)
                {
                    op2 = IntLiteral2Int(addExp2->v, buffer);
                }
                else if (addExp2->t == Type::FloatLiteral)
                {
                    op2 = FloatLiteral2Float(addExp2->v, buffer);
                }
                else
                {
                    op2 = Operand(addExp2->v, addExp2->t);
                }

                if (term->token.type == TokenType::LSS)
                {
                    if (op1.type == Type::Int && op2.type == Type::Int)
                    {
                        buffer.push_back(new Instruction(op1, op2, op1, Operator::lss));
                    }
                    else if (op1.type == Type::Float && op2.type == Type::Int)
                    {

                        Operand tmpVar = Operand(getTmp(), Type::Float);
                        buffer.push_back(new Instruction({op2}, {}, {tmpVar}, {Operator::cvt_i2f}));
                        buffer.push_back(new Instruction({op1}, {tmpVar}, {op1}, {Operator::flss}));
                    }
                    else if (op1.type == Type::Float && op2.type == Type::Float)
                    {

                        buffer.push_back(new Instruction(op1, op2, op1, Operator::flss));
                    }
                    else
                    {
                        assert(0 && "to be continue");
                    }
                }
                else if (term->token.type == TokenType::GTR)
                {
                    if (op1.type == Type::Int && op2.type == Type::Int)
                    {
                        buffer.push_back(new Instruction(op1, op2, op1, Operator::gtr));
                    }
                    else
                    {
                        assert(0 && "to be continue");
                    }
                }
                else if (term->token.type == TokenType::LEQ)
                {
                    if (op1.type == Type::Int && op2.type == Type::Int)
                    {
                        buffer.push_back(new Instruction(op1, op2, op1, Operator::leq));
                    }
                    else
                    {
                        assert(0 && "to be continue");
                    }
                }
                else if (term->token.type == TokenType::GEQ)
                {
                    if (op1.type == Type::Int && op2.type == Type::Int)
                    {
                        buffer.push_back(new Instruction(op1, op2, op1, Operator::geq));
                    }
                    else
                    {
                        assert(0 && "to be continue");
                    }
                }
                else
                    assert(0 && "RelExp op error");
            }
        }

        root->t = op1.type;
        root->v = op1.name;
    }
}

void frontend::Analyzer::analyzeUnaryOp(UnaryOp *root)
{

    GET_NODE_PTR(Term, term, 0)
    root->op = term->token.type;
}

ir::Operand frontend::Analyzer::IntLiteral2Int(string val, vector<ir::Instruction *> &buffer)
{

    Operand opd = {getTmp(), Type::Int};
    buffer.push_back(new Instruction({val, Type::IntLiteral}, {}, {opd}, {Operator::def}));
    return opd;
}

ir::Operand frontend::Analyzer::FloatLiteral2Float(string val, vector<ir::Instruction *> &buffer)
{

    Operand opd = {getTmp(), Type::Float};
    buffer.push_back(new Instruction({val, Type::FloatLiteral}, {}, {opd}, {Operator::fdef}));
    return opd;
}

std::string frontend::Analyzer::getTmp()
{

    return "t" + std::to_string(tmp_cnt++);
}
