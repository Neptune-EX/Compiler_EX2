#include "front/lexical.h"

#include <map>
#include <cassert>
#include <string>

#define TODO assert(0 && "todo")

std::string frontend::toString(State s)
{
    switch (s)
    {
    case State::Empty:
        return "Empty";
    case State::Ident:
        return "Ident";
    case State::IntLiteral:
        return "IntLiteral";
    case State::FloatLiteral:
        return "FloatLiteral";
    case State::op:
        return "op";
    default:
        assert(0 && "invalid State");
    }
    return "";
}

std::set<std::string> frontend::keywords = {"const", "int", "float", "if", "else", "while", "continue", "break", "return", "void"};

std::string preproccess(std::ifstream &fin)
{

    std::string res;
    std::string curLine;
    bool isInMulCom = false;
    while (std::getline(fin, curLine))
    {
        int mulEndPos = 0;
        if (isInMulCom)
        {
            mulEndPos = curLine.find("*/");
            if (mulEndPos != std::string::npos)
            {
                isInMulCom = false;
                curLine.erase(0, mulEndPos + 2);
            }
            else
                continue;
        }

        while (curLine.find("//") != std::string::npos || curLine.find("/*") != std::string::npos)
        {
            int sinPos = curLine.find("//");
            int mulStartPos = curLine.find("/*");
            if (sinPos != std::string::npos && mulStartPos == std::string::npos)
                curLine.erase(sinPos);
            else if (sinPos == std::string::npos && mulStartPos != std::string::npos)
            {

                mulEndPos = curLine.find("*/", mulStartPos + 2);
                if (mulEndPos != std::string::npos)

                    curLine.erase(mulStartPos, mulEndPos - mulStartPos + 2);
                else
                {
                    isInMulCom = true;
                    curLine.erase(mulStartPos);
                }
            }
            else
            {
                if (sinPos < mulStartPos)
                    curLine.erase(sinPos);
                else
                {
                    mulEndPos = curLine.find("*/");
                    if (mulEndPos != std::string::npos)
                        curLine.erase(mulStartPos, mulEndPos - mulStartPos + 2);
                    else
                    {
                        isInMulCom = true;
                        curLine.erase(mulStartPos);
                    }
                }
            }
        }
        res += curLine + "\n";
    }
    return res;
}

bool isoperator(char c)
{

    return c == '+' || c == '-' || c == '*' || c == '/' ||
           c == '%' || c == '<' || c == '>' || c == '=' ||
           c == ':' || c == ';' || c == '(' || c == ')' ||
           c == '[' || c == ']' || c == '{' || c == '}' ||
           c == '!' || c == '&' || c == '|' || c == ',';
}

frontend::TokenType getIdentType(std::string s)
{

    if (s == "const")
        return frontend::TokenType::CONSTTK;
    else if (s == "int")
        return frontend::TokenType::INTTK;
    else if (s == "float")
        return frontend::TokenType::FLOATTK;
    else if (s == "if")
        return frontend::TokenType::IFTK;
    else if (s == "else")
        return frontend::TokenType::ELSETK;
    else if (s == "while")
        return frontend::TokenType::WHILETK;
    else if (s == "continue")
        return frontend::TokenType::CONTINUETK;
    else if (s == "break")
        return frontend::TokenType::BREAKTK;
    else if (s == "return")
        return frontend::TokenType::RETURNTK;
    else if (s == "void")
        return frontend::TokenType::VOIDTK;
    else
        return frontend::TokenType::IDENFR;
}

frontend::TokenType getOpType(std::string s)
{

    if (s == "+")
        return frontend::TokenType::PLUS;
    else if (s == "-")
        return frontend::TokenType::MINU;
    else if (s == "*")
        return frontend::TokenType::MULT;
    else if (s == "/")
        return frontend::TokenType::DIV;
    else if (s == "%")
        return frontend::TokenType::MOD;
    else if (s == "<")
        return frontend::TokenType::LSS;
    else if (s == ">")
        return frontend::TokenType::GTR;
    else if (s == ":")
        return frontend::TokenType::COLON;
    else if (s == "=")
        return frontend::TokenType::ASSIGN;
    else if (s == ";")
        return frontend::TokenType::SEMICN;
    else if (s == ",")
        return frontend::TokenType::COMMA;
    else if (s == "(")
        return frontend::TokenType::LPARENT;
    else if (s == ")")
        return frontend::TokenType::RPARENT;
    else if (s == "[")
        return frontend::TokenType::LBRACK;
    else if (s == "]")
        return frontend::TokenType::RBRACK;
    else if (s == "{")
        return frontend::TokenType::LBRACE;
    else if (s == "}")
        return frontend::TokenType::RBRACE;
    else if (s == "!")
        return frontend::TokenType::NOT;
    else if (s == "<=")
        return frontend::TokenType::LEQ;
    else if (s == ">=")
        return frontend::TokenType::GEQ;
    else if (s == "==")
        return frontend::TokenType::EQL;
    else if (s == "!=")
        return frontend::TokenType::NEQ;
    else if (s == "&&")
        return frontend::TokenType::AND;
    else if (s == "||")
        return frontend::TokenType::OR;
    else
        assert(0 && "invalid operator!");
}

bool isDoubleWidthOperator(std::string s)
{

    return s == ">=" || s == "<=" || s == "==" ||
           s == "!=" || s == "&&" || s == "||";
}

frontend::DFA::DFA() : cur_state(frontend::State::Empty), cur_str() {}

frontend::DFA::~DFA() {}

bool frontend::DFA::next(char input, Token &buf)
{
#ifdef DEBUG_DFA
#include <iostream>
    std::cout << "in state [" << toString(cur_state) << "], input = \'" << input << "\', str = " << cur_str << std::endl;
#endif

    bool flag = false;
    switch (cur_state)
    {
    case frontend::State::Empty:
        if (isspace(input))
            reset();
        else if (isalpha(input) || input == '_')
        {
            cur_state = frontend::State::Ident;
            cur_str += input;
        }
        else if (isdigit(input))
        {
            cur_state = frontend::State::IntLiteral;
            cur_str += input;
        }

        else if (input == '.')
        {
            cur_state = frontend::State::FloatLiteral;
            cur_str += input;
        }
        else if (isoperator(input))
        {
            cur_state = frontend::State::op;
            cur_str += input;
        }
        else
            assert(0 && "invalid input");
        break;
    case frontend::State::Ident:
        if (isspace(input))
        {
            buf.type = getIdentType(cur_str);
            buf.value = cur_str;
            reset();
            flag = true;
        }
        else if (isalpha(input) || isdigit(input) || input == '_')
        {
            cur_state = frontend::State::Ident;
            cur_str += input;
        }
        else if (isoperator(input))
        {
            buf.type = getIdentType(cur_str);
            buf.value = cur_str;
            cur_str = "";
            cur_state = frontend::State::op;
            cur_str += input;
            flag = true;
        }
        else
            assert(0 && "invalid input");
        break;
    case frontend::State::IntLiteral:
        if (isspace(input))
        {
            buf.type = frontend::TokenType::INTLTR;
            buf.value = cur_str;
            reset();
            flag = true;
        }
        else if (isdigit(input) || isalpha(input))
        {
            cur_state = frontend::State::IntLiteral;
            cur_str += input;
        }
        else if (input == '.')
        {
            cur_state = frontend::State::FloatLiteral;
            cur_str += input;
        }
        else if (isoperator(input))
        {
            buf.type = frontend::TokenType::INTLTR;
            buf.value = cur_str;
            cur_str = "";
            cur_state = frontend::State::op;
            cur_str += input;
            flag = true;
        }
        else
            assert(0 && "invalid input");
        break;
    case frontend::State::FloatLiteral:
        if (isspace(input))
        {
            buf.type = frontend::TokenType::FLOATLTR;
            buf.value = cur_str;
            reset();
            flag = true;
        }
        else if (isdigit(input))
        {
            cur_state = frontend::State::FloatLiteral;
            cur_str += input;
        }
        else if (isoperator(input))
        {
            buf.type = frontend::TokenType::FLOATLTR;
            buf.value = cur_str;
            cur_str = "";
            cur_state = frontend::State::op;
            cur_str += input;
            flag = true;
        }
        else
            assert(0 && "invalid input");
        break;
    case frontend::State::op:
        if (isspace(input))
        {
            buf.type = getOpType(cur_str);
            buf.value = cur_str;
            reset();
            flag = true;
        }
        else if (isalpha(input) || input == '_')
        {
            buf.type = getOpType(cur_str);
            buf.value = cur_str;
            cur_str = "";
            cur_state = frontend::State::Ident;
            cur_str += input;
            flag = true;
        }
        else if (isdigit(input))
        {
            buf.type = getOpType(cur_str);
            buf.value = cur_str;
            cur_str = "";
            cur_state = frontend::State::IntLiteral;
            cur_str += input;
            flag = true;
        }
        else if (isoperator(input))
        {
            if (isDoubleWidthOperator(cur_str + input))
                cur_str += input;
            else
            {
                buf.type = getOpType(cur_str);
                buf.value = cur_str;
                cur_str = "";
                cur_state = frontend::State::op;
                cur_str += input;
                flag = true;
            }
        }
        else if (input == '.')
        {
            buf.type = getOpType(cur_str);
            buf.value = cur_str;
            cur_str = "";
            cur_state = frontend::State::FloatLiteral;
            cur_str += input;
            flag = true;
        }
        else
            assert(0 && "invalid input");
        break;
    default:
        assert(0 && "invalid state");
        break;
    }

    return flag;
}

void frontend::DFA::reset()
{
    cur_state = State::Empty;
    cur_str = "";
}

frontend::Scanner::Scanner(std::string filename) : fin(filename)
{
    if (!fin.is_open())
    {
        assert(0 && "in Scanner constructor, input file cannot open");
    }
}

frontend::Scanner::~Scanner()
{
    fin.close();
}

std::vector<frontend::Token> frontend::Scanner::run()
{

    std::vector<Token> tokens;
    Token tk;
    DFA dfa;
    std::string str = preproccess(fin);
    str += "\n";
    for (char c : str)
    {
        if (dfa.next(c, tk))
        {
            tokens.push_back(tk);
#ifdef DEBUG_SCANNER
#include <iostream>
            std::cout << "token: " << toString(tk.type) << "\t" << tk.value << std::endl;
#endif
        }
    }
    return tokens;
}
