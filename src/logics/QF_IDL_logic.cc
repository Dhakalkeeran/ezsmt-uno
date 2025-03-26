#include "logic.h"
#include "QF_IDL_logic.h"
#include "glog/logging.h"
#include "program.h"
#include <numeric>
#include "smtstringhelpers.h"

string QF_IDL_logic::SMT_LOGIC_NAME() { return "QF_IDL";}

string QF_IDL_logic::getDiffAssertionStatement(TheoryStatement* statement) {
    if (statement->leftElements.size() > 1) {
        LOG(ERROR) << "Invalid syntax for diff statment. More than one term not allowed." << endl;
    }

    auto element = statement->leftElements.front();
    auto term = element->terms.front();

    // lambda counter function for recursion on counting symbolic terms (variables) within nested expression terms
    std::function<void(ExpressionTerm*, int&)> countVariables = [&](ExpressionTerm* expressionTerm, int& count) {
        for (auto child: expressionTerm->children) {
            if (auto nestedExpression = dynamic_cast<ExpressionTerm*>(child)) {
                countVariables(nestedExpression, count);
            }
            else if (auto symbolicTerm = dynamic_cast<SymbolicTerm*>(child)) {
                if (++count > 2) {
                    LOG(ERROR) << "Invalid syntax for diff statment. More than two variables not allowed." << endl;
                }
            }
        }
    };

    // check if there are more than two variables
    if (auto expressionTerm = dynamic_cast<ExpressionTerm*>(term)) {
        int variableCount = 0;
        countVariables(expressionTerm, variableCount);     

        if (expressionTerm->operation->name != "-") {
            LOG(ERROR) << "Invalid syntax for diff statment. Only difference operation is allowed." << endl;
        }
    }

    string operation = statement->operation->name;
    if (operation != "<=") {
        LOG(ERROR) << "Invalid syntax for diff statment. Only <= operator is allowed with IDL logic." << endl;
    }

    auto diffStatement = SMT::Expr(operation, {toString(element), SMT::ToString(statement->rightTerm)});
    return diffStatement;
}

void QF_IDL_logic::getAssertionStatements(std::ostringstream &output) {
    for (const auto statement : statements) {
        string assertionStatement;
        if (statement->symbolicTerm->name == "diff")  {
            assertionStatement = getDiffAssertionStatement(statement);
        }
        else if (statement->symbolicTerm->name == "dom") {
            assertionStatement = getDomAssertionStatement(statement);
        }
        else {
            LOG(ERROR) << "The " << statement->symbolicTerm->name << " statement is not supported with the " << SMT_LOGIC_NAME() << " logic.";
        }

        string assertion = SMT::Assert(SMT::Expr("=", {SMT::Var(statement->statementAtom), assertionStatement}));
        output << assertion;
    }
}