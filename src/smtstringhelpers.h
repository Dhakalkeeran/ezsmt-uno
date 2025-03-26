#ifndef SMTSTRINGHELPERS_H_
#define SMTSTRINGHELPERS_H_

#include <list>
#include <regex>
#include <sstream>
#include <string>
#include "theory.h"
#include "program.h"

using namespace std;


class SMT {
public:
    static string Var(Atom* atom) {
        if (!atom->name) {
            return escape(to_string(atom->id));
        }

        string smtName = atom->name;
        if (atom->isLevelRankingConstraint()) {
            return smtName.substr(LEVEL_RANKING_ATOM_PREFIX.length());
        }

        return escape(smtName);
    }

    static string Var(LevelRankingVariable &variable) {
        return escape(variable.GetSmtName());
    }

    static string Var(MinimizationStatement *statement) {
        return escape(statement->getAtomName());
    }

    static  string Var(SymbolicTerm* term) {
        return escape(term->name);
    }

    static string VarUnsafe(string name) {
        return escape(name);
    }

    static string Unescape(string variableName) {
        bool alreadyEscaped = variableName.front() == '|' && variableName.back() == '|';
        if (alreadyEscaped && variableName.size() > 1) {
            return variableName.substr(1, variableName.size() - 2);
        } else {
            return variableName;
        }
    }

    static string Expr(string operation, const list<string>& arguments, bool passThoughIfSingleArg = false) {
        if (passThoughIfSingleArg && arguments.size() == 1) {
            return arguments.front();
        }

        ostringstream output;
        output << "(" << operation;
        for (auto arg : arguments) {
            output << " " << arg;
        }
        output << ")";
        return output.str();
    }

    static string Assert(string expression) {
        ostringstream output;
        output << "(assert " << expression << ")" << endl;
        return output.str();
    }

    static string DeclareConst(string variableName, string type) {
        ostringstream output;
        output << "(declare-const " << escape(variableName) << " " << type << ")" << endl;
        return output.str();
    }

    static string Not(string expression) {
        return Expr("not", {expression});
    }

    static string And(const list<string>& arguments) {
        return Expr("and", arguments);
    }

    static string Or(const list<string>& arguments) {
        return Expr("or", arguments);
    }

    static string ToString(ITheoryTerm* term) {
        if (auto t = dynamic_cast<NumericTerm*>(term)) {
            return to_string(t->value);
        } else if (auto t = dynamic_cast<RealTerm*>(term)) {
            return to_string(t->value);
        } else if (auto t = dynamic_cast<SymbolicTerm*>(term)) {
            return escape(t->name);
        } else if (auto t = dynamic_cast<TupleTerm*>(term)) {
            if (t->type == PARENTHESES) {
                return string("(") + ToString(*(t->children.begin())) + ")";
            }
        } else if (auto t = dynamic_cast<ExpressionTerm*>(term)) {
            list<string> childTerms;
            for (auto term : t->children) {
                childTerms.push_back(ToString(term));
            }
            return SMT::Expr(t->operation->name, childTerms);
        }

        LOG(ERROR) << "Unsupported term type";
    }
private:
    static string escape(string name) {
        bool alreadyEscaped = name.front() == '|' && name.back() == '|';
        if (alreadyEscaped) {
            return name;
        }

        if (regex_match(name, regex(".*[(),0-9]+.*"))) {
            return "|" + name + "|";
        } else {
            return name;
        }
    }

};


#endif // SMTSTRINGHELPERS_H_
