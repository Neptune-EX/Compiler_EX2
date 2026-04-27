#include "front/syntax.h"
#include <iostream>
#include <cassert>

using frontend::Parser;

#define TODO assert(0 && "todo")
#define saveChildrenNum int curChildrenNums = res->children.size()
#define saveIndex int lastIndex = index

Parser::Parser(const std::vector<frontend::Token> &tokens) : index(0), token_stream(tokens) {}

Parser::~Parser() {}

frontend::CompUnit *Parser::get_abstract_syntax_tree()
{

    return parseCompUnit(nullptr);
}

void Parser::log(AstNode *node)
{
#ifdef DEBUG_PARSER
    std::cout << "in parse" << toString(node->type) << ", cur_token_type::" << toString(token_stream[index].type) << ", token_val::" << token_stream[index].value << '\n';
#endif
}

frontend::CompUnit *Parser::parseCompUnit(AstNode *root)
{
    CompUnit *res = new CompUnit(root);

    bool isDecl = false;
    bool isFuncDef = false;
    saveIndex;
    saveChildrenNum;

    if (matchDecl().count(token_stream[index].type))
    {
        isDecl = parseDecl(res);
        if (!isDecl)
            undo(lastIndex, res, curChildrenNums);
    }

    if (!isDecl && matchFuncDef().count(token_stream[index].type))
        isFuncDef = parseFuncDef(res);

    if (!isDecl && !isFuncDef)
        assert(0 && "error in parseCompUnit");

    if (matchCompUnit().count(token_stream[index].type))
        parseCompUnit(res);

    return res;
}

bool Parser::parseDecl(AstNode *root)
{
    Decl *res = new Decl(root);
    bool isConstDecl = false;
    bool isVarDecl = false;
    if (matchConstDecl().count(token_stream[index].type))
        isConstDecl = parseConstDecl(res);
    else if (matchVarDecl().count(token_stream[index].type))
        isVarDecl = parseVarDecl(res);
    if (!isConstDecl && !isVarDecl)
        return false;
    return true;
}

bool Parser::parseConstDecl(AstNode *root)
{
    ConstDecl *res = new ConstDecl(root);
    new Term(token_stream[index++], res);
    parseBType(res);
    parseConstDef(res);
    while (token_stream[index].type == frontend::TokenType::COMMA)
    {
        new Term(token_stream[index++], res);
        parseConstDef(res);
    }
    new Term(token_stream[index++], res);
    return true;
}

bool Parser::parseBType(AstNode *root)
{
    BType *res = new BType(root);
    if (token_stream[index].type == frontend::TokenType::INTTK)
        new Term(token_stream[index++], res);
    else if (token_stream[index].type == frontend::TokenType::FLOATTK)
        new Term(token_stream[index++], res);
    return true;
}

bool Parser::parseConstDef(AstNode *root)
{
    ConstDef *res = new ConstDef(root);
    new Term(token_stream[index++], res);
    while (token_stream[index].type == frontend::TokenType::LBRACK)
    {
        new Term(token_stream[index++], res);
        parseConstExp(res);
        new Term(token_stream[index++], res);
    }
    new Term(token_stream[index++], res);
    parseConstInitVal(res);
    return true;
}

bool Parser::parseConstInitVal(AstNode *root)
{
    ConstInitVal *res = new ConstInitVal(root);
    if (matchConstExp().count(token_stream[index].type))
        parseConstExp(res);
    if (token_stream[index].type == frontend::TokenType::LBRACE)
    {
        new Term(token_stream[index++], res);
        if (matchConstInitVal().count(token_stream[index].type))
        {
            parseConstInitVal(res);
            while (token_stream[index].type == frontend::TokenType::COMMA)
            {
                new Term(token_stream[index++], res);
                parseConstInitVal(res);
            }
        }
        new Term(token_stream[index++], res);
    }

    return true;
}

bool Parser::parseVarDecl(AstNode *root)
{
    VarDecl *res = new VarDecl(root);
    parseBType(res);
    parseVarDef(res);
    while (token_stream[index].type == frontend::TokenType::COMMA)
    {
        new Term(token_stream[index++], res);
        parseVarDef(res);
    }
    if (token_stream[index].type != frontend::TokenType::SEMICN)
        return false;
    new Term(token_stream[index++], res);

    return true;
}

bool Parser::parseVarDef(AstNode *root)
{
    VarDef *res = new VarDef(root);
    new Term(token_stream[index++], res);
    while (token_stream[index].type == frontend::TokenType::LBRACK)
    {
        new Term(token_stream[index++], res);
        parseConstExp(res);
        new Term(token_stream[index++], res);
    }
    if (token_stream[index].type == frontend::TokenType::ASSIGN)
    {
        new Term(token_stream[index++], res);
        parseInitVal(res);
    }
    return true;
}

bool Parser::parseInitVal(AstNode *root)
{
    InitVal *res = new InitVal(root);

    if (matchExp().count(token_stream[index].type))
        parseExp(res);
    if (token_stream[index].type == frontend::TokenType::LBRACE)
    {
        new Term(token_stream[index++], res);
        if (matchInitVal().count(token_stream[index].type))
        {
            parseInitVal(res);
            while (token_stream[index].type == frontend::TokenType::COMMA)
            {
                new Term(token_stream[index++], res);
                parseInitVal(res);
            }
        }
        new Term(token_stream[index++], res);
    }
    return true;
}

bool Parser::parseFuncDef(AstNode *root)
{
    FuncDef *res = new FuncDef(root);
    parseFuncType(res);
    new Term(token_stream[index++], res);
    new Term(token_stream[index++], res);
    if (matchFuncFParams().count(token_stream[index].type))
        parseFuncFParams(res);
    new Term(token_stream[index++], res);
    parseBlock(res);
    return true;
}

bool Parser::parseFuncType(AstNode *root)
{
    FuncType *res = new FuncType(root);

    if (token_stream[index].type == frontend::TokenType::VOIDTK)
        new Term(token_stream[index++], res);
    else if (token_stream[index].type == frontend::TokenType::INTTK)
        new Term(token_stream[index++], res);
    else if (token_stream[index].type == frontend::TokenType::FLOATTK)
        new Term(token_stream[index++], res);

    return true;
}

bool Parser::parseFuncFParam(AstNode *root)
{
    FuncFParam *res = new FuncFParam(root);
    parseBType(res);
    new Term(token_stream[index++], res);
    if (token_stream[index].type == frontend::TokenType::LBRACK)
    {
        new Term(token_stream[index++], res);
        new Term(token_stream[index++], res);
        while (token_stream[index].type == frontend::TokenType::LBRACK)
        {
            new Term(token_stream[index++], res);
            parseExp(res);
            new Term(token_stream[index++], res);
        }
    }
    return true;
}

bool Parser::parseFuncFParams(AstNode *root)
{
    FuncFParams *res = new FuncFParams(root);
    parseFuncFParam(res);
    while (token_stream[index].type == frontend::TokenType::COMMA)
    {
        new Term(token_stream[index++], res);
        parseFuncFParam(res);
    }
    return true;
}

bool Parser::parseBlock(AstNode *root)
{
    Block *res = new Block(root);
    new Term(token_stream[index++], res);
    while (matchBlockItem().count(token_stream[index].type))
        parseBlockItem(res);
    new Term(token_stream[index++], res);
    return true;
}

bool Parser::parseBlockItem(AstNode *root)
{
    BlockItem *res = new BlockItem(root);
    if (matchDecl().count(token_stream[index].type))
        parseDecl(res);
    else if (matchStmt().count(token_stream[index].type))
        parseStmt(res);
    return true;
}

bool Parser::parseStmt(AstNode *root)
{
    Stmt *res = new Stmt(root);
    saveIndex;
    saveChildrenNum;

    if (matchLVal().count(token_stream[index].type))
    {
        parseLVal(res);
        if (token_stream[index].type != frontend::TokenType::ASSIGN)
        {
            undo(lastIndex, res, curChildrenNums);
            goto BlockCase;
        }
        new Term(token_stream[index++], res);
        parseExp(res);
        new Term(token_stream[index++], res);
        return true;
    }

BlockCase:
    if (matchBlock().count(token_stream[index].type))
        parseBlock(res);
    else if (token_stream[index].type == frontend::TokenType::IFTK)
    {
        new Term(token_stream[index++], res);
        new Term(token_stream[index++], res);
        parseCond(res);
        new Term(token_stream[index++], res);
        parseStmt(res);
        if (token_stream[index].type == frontend::TokenType::ELSETK)
        {
            new Term(token_stream[index++], res);
            parseStmt(res);
        }
    }
    else if (token_stream[index].type == frontend::TokenType::WHILETK)
    {
        new Term(token_stream[index++], res);
        new Term(token_stream[index++], res);
        parseCond(res);
        new Term(token_stream[index++], res);
        parseStmt(res);
    }
    else if (token_stream[index].type == frontend::TokenType::BREAKTK)
    {
        new Term(token_stream[index++], res);
        new Term(token_stream[index++], res);
    }
    else if (token_stream[index].type == frontend::TokenType::CONTINUETK)
    {
        new Term(token_stream[index++], res);
        new Term(token_stream[index++], res);
    }
    else if (token_stream[index].type == frontend::TokenType::RETURNTK)
    {
        new Term(token_stream[index++], res);

        if (matchExp().count(token_stream[index].type))
            parseExp(res);

        new Term(token_stream[index++], res);
    }
    else if (matchExp().count(token_stream[index].type))
    {
        parseExp(res);
        new Term(token_stream[index++], res);
    }
    else if (token_stream[index].type == frontend::TokenType::SEMICN)
        new Term(token_stream[index++], res);

    return true;
}

bool Parser::parseExp(AstNode *root)
{
    Exp *res = new Exp(root);
    parseAddExp(res);
    return true;
}

bool Parser::parseCond(AstNode *root)
{
    Cond *res = new Cond(root);
    parseLOrExp(res);
    return true;
}

bool Parser::parseLVal(AstNode *root)
{
    LVal *res = new LVal(root);
    new Term(token_stream[index++], res);
    while (token_stream[index].type == frontend::TokenType::LBRACK)
    {
        new Term(token_stream[index++], res);
        parseExp(res);
        new Term(token_stream[index++], res);
    }
    return true;
}

bool Parser::parseNumber(AstNode *root)
{
    Number *res = new Number(root);
    new Term(token_stream[index++], res);
    return true;
}

bool Parser::parsePrimaryExp(AstNode *root)
{
    PrimaryExp *res = new PrimaryExp(root);
    if (token_stream[index].type == frontend::TokenType::LPARENT)
    {
        new Term(token_stream[index++], res);
        parseExp(res);
        new Term(token_stream[index++], res);
    }
    else if (matchLVal().count(token_stream[index].type))
        parseLVal(res);
    else if (matchNumber().count(token_stream[index].type))
        parseNumber(res);
    return true;
}

bool Parser::parseUnaryExp(AstNode *root)
{

    UnaryExp *res = new UnaryExp(root);
    saveIndex;
    saveChildrenNum;

    if (token_stream[index].type == frontend::TokenType::IDENFR)
    {
        new Term(token_stream[index++], res);
        if (token_stream[index].type != frontend::TokenType::LPARENT)
        {
            undo(lastIndex, res, curChildrenNums);
            goto PrimaryExpCase;
        }
        new Term(token_stream[index++], res);
        if (matchFuncRParams().count(token_stream[index].type))
            parseFuncRParams(res);
        new Term(token_stream[index++], res);
        return true;
    }

PrimaryExpCase:
    if (matchPrimaryExp().count(token_stream[index].type))
    {
        parsePrimaryExp(res);
        return true;
    }

    if (matchUnaryOp().count(token_stream[index].type))
    {
        parseUnaryOp(res);
        parseUnaryExp(res);
    }

    return true;
}

bool Parser::parseUnaryOp(AstNode *root)
{
    UnaryOp *res = new UnaryOp(root);

    if (token_stream[index].type != frontend::TokenType::PLUS && token_stream[index].type != frontend::TokenType::MINU && token_stream[index].type != frontend::TokenType::NOT)
        return false;
    new Term(token_stream[index++], res);

    return true;
}

bool Parser::parseFuncRParams(AstNode *root)
{
    FuncRParams *res = new FuncRParams(root);
    parseExp(res);
    while (token_stream[index].type == frontend::TokenType::COMMA)
    {
        new Term(token_stream[index++], res);
        parseExp(res);
    }
    return true;
}

bool Parser::parseMulExp(AstNode *root)
{
    MulExp *res = new MulExp(root);
    parseUnaryExp(res);
    while (token_stream[index].type == frontend::TokenType::MULT || token_stream[index].type == frontend::TokenType::DIV || token_stream[index].type == frontend::TokenType::MOD)
    {
        new Term(token_stream[index++], res);
        parseUnaryExp(res);
    }
    return true;
}

bool Parser::parseAddExp(AstNode *root)
{
    AddExp *res = new AddExp(root);
    parseMulExp(res);
    while (token_stream[index].type == frontend::TokenType::PLUS || token_stream[index].type == frontend::TokenType::MINU)
    {
        new Term(token_stream[index++], res);
        parseMulExp(res);
    }
    return true;
}

bool Parser::parseRelExp(AstNode *root)
{
    RelExp *res = new RelExp(root);
    parseAddExp(res);
    while (token_stream[index].type == frontend::TokenType::LSS || token_stream[index].type == frontend::TokenType::GTR || token_stream[index].type == frontend::TokenType::LEQ || token_stream[index].type == frontend::TokenType::GEQ)
    {
        new Term(token_stream[index++], res);
        parseAddExp(res);
    }
    return true;
}

bool Parser::parseEqExp(AstNode *root)
{
    EqExp *res = new EqExp(root);
    parseRelExp(res);
    while (token_stream[index].type == frontend::TokenType::EQL || token_stream[index].type == frontend::TokenType::NEQ)
    {
        new Term(token_stream[index++], res);
        parseRelExp(res);
    }
    return true;
}

bool Parser::parseLAndExp(AstNode *root)
{
    LAndExp *res = new LAndExp(root);
    parseEqExp(res);
    if (token_stream[index].type == frontend::TokenType::AND)
    {
        new Term(token_stream[index++], res);
        parseLAndExp(res);
    }
    return true;
}

bool Parser::parseLOrExp(AstNode *root)
{
    LOrExp *res = new LOrExp(root);
    parseLAndExp(res);
    if (token_stream[index].type == frontend::TokenType::OR)
    {
        new Term(token_stream[index++], res);
        parseLOrExp(res);
    }
    return true;
}

bool Parser::parseConstExp(AstNode *root)
{
    ConstExp *res = new ConstExp(root);
    parseAddExp(res);
    return true;
}

std::set<frontend::TokenType> Parser::matchCompUnit()
{
    return {frontend::TokenType::CONSTTK, frontend::TokenType::INTTK,
            frontend::TokenType::FLOATTK, frontend::TokenType::VOIDTK};
}

std::set<frontend::TokenType> Parser::matchDecl()
{
    return {frontend::TokenType::CONSTTK, frontend::TokenType::INTTK,
            frontend::TokenType::FLOATTK};
}

std::set<frontend::TokenType> Parser::matchConstDecl()
{
    return {frontend::TokenType::CONSTTK};
}

std::set<frontend::TokenType> Parser::matchBType()
{
    return {frontend::TokenType::INTTK, frontend::TokenType::FLOATTK};
}

std::set<frontend::TokenType> Parser::matchConstDef()
{
    return {frontend::TokenType::IDENFR};
}

std::set<frontend::TokenType> Parser::matchConstInitVal()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT,
            frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT, frontend::TokenType::LBRACE};
}

std::set<frontend::TokenType> Parser::matchVarDecl()
{
    return {frontend::TokenType::INTTK, frontend::TokenType::FLOATTK};
}

std::set<frontend::TokenType> Parser::matchVarDef()
{
    return {frontend::TokenType::IDENFR};
}

std::set<frontend::TokenType> Parser::matchInitVal()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT,
            frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT, frontend::TokenType::LBRACE};
}

std::set<frontend::TokenType> Parser::matchFuncDef()
{
    return {frontend::TokenType::VOIDTK, frontend::TokenType::INTTK,
            frontend::TokenType::FLOATTK};
}

std::set<frontend::TokenType> Parser::matchFuncType()
{
    return {frontend::TokenType::VOIDTK, frontend::TokenType::INTTK,
            frontend::TokenType::FLOATTK};
}

std::set<frontend::TokenType> Parser::matchFuncFParam()
{
    return {frontend::TokenType::INTTK, frontend::TokenType::FLOATTK};
}

std::set<frontend::TokenType> Parser::matchFuncFParams()
{
    return {frontend::TokenType::INTTK, frontend::TokenType::FLOATTK};
}

std::set<frontend::TokenType> Parser::matchBlock()
{
    return {frontend::TokenType::LBRACE};
}

std::set<frontend::TokenType> Parser::matchBlockItem()
{

    return {frontend::TokenType::CONSTTK, frontend::TokenType::INTTK,
            frontend::TokenType::FLOATTK, frontend::TokenType::IDENFR,
            frontend::TokenType::IFTK, frontend::TokenType::WHILETK,
            frontend::TokenType::BREAKTK, frontend::TokenType::CONTINUETK,
            frontend::TokenType::RETURNTK, frontend::TokenType::SEMICN,
            frontend::TokenType::INTLTR, frontend::TokenType::FLOATLTR,
            frontend::TokenType::LPARENT, frontend::TokenType::PLUS,
            frontend::TokenType::MINU, frontend::TokenType::NOT,
            frontend::TokenType::LBRACE};
}

std::set<frontend::TokenType> Parser::matchStmt()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::LBRACE,
            frontend::TokenType::IFTK, frontend::TokenType::WHILETK,
            frontend::TokenType::BREAKTK, frontend::TokenType::CONTINUETK,
            frontend::TokenType::RETURNTK, frontend::TokenType::SEMICN,
            frontend::TokenType::INTLTR, frontend::TokenType::FLOATLTR,
            frontend::TokenType::LPARENT, frontend::TokenType::PLUS,
            frontend::TokenType::MINU, frontend::TokenType::NOT};
}

std::set<frontend::TokenType> Parser::matchExp()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT,
            frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT};
}

std::set<frontend::TokenType> Parser::matchCond()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT,
            frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT};
}

std::set<frontend::TokenType> Parser::matchLVal()
{
    return {frontend::TokenType::IDENFR};
}

std::set<frontend::TokenType> Parser::matchNumber()
{
    return {frontend::TokenType::INTLTR, frontend::TokenType::FLOATLTR};
}

std::set<frontend::TokenType> Parser::matchPrimaryExp()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT};
}

std::set<frontend::TokenType> Parser::matchUnaryExp()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT,
            frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT};
}

std::set<frontend::TokenType> Parser::matchUnaryOp()
{
    return {frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT};
}

std::set<frontend::TokenType> Parser::matchFuncRParams()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT,
            frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT};
}

std::set<frontend::TokenType> Parser::matchMulExp()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT,
            frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT};
}

std::set<frontend::TokenType> Parser::matchAddExp()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT,
            frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT};
}

std::set<frontend::TokenType> Parser::matchRelExp()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT,
            frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT};
}

std::set<frontend::TokenType> Parser::matchEqExp()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT,
            frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT};
}

std::set<frontend::TokenType> Parser::matchLAndExp()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT,
            frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT};
}

std::set<frontend::TokenType> Parser::matchLOrExp()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT,
            frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT};
}

std::set<frontend::TokenType> Parser::matchConstExp()
{
    return {frontend::TokenType::IDENFR, frontend::TokenType::INTLTR,
            frontend::TokenType::FLOATLTR, frontend::TokenType::LPARENT,
            frontend::TokenType::PLUS, frontend::TokenType::MINU,
            frontend::TokenType::NOT};
}

void Parser::undo(int _lastIndex, AstNode *_res, int _curChildrenNums)
{
    index = _lastIndex;
    while (_res->children.size() > _curChildrenNums)
        _res->children.pop_back();
    return;
}
