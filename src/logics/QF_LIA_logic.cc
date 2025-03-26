#include "logic.h"
#include "QF_LIA_logic.h"
#include "glog/logging.h"
#include "program.h"
#include <numeric>
#include "smtstringhelpers.h"

string QF_LIA_logic::SMT_LOGIC_NAME() { return "QF_LIA"; }

void QF_LIA_logic::processTheoryStatements(list<TheoryStatement*> statements) {
    this->statements = statements;

    // lambda helper function for recursion on nested expression terms
    std::function<void(ExpressionTerm*)> helper = [&](ExpressionTerm* expressionTerm) {
        for (auto exp: expressionTerm->children) {
            if (auto s = dynamic_cast<SymbolicTerm*>(exp)) {
                this->symbolicTerms[s->id] = s;
            }
            else if (auto s = dynamic_cast<ExpressionTerm*>(exp)) {
                helper(s);
            }
        }
    };

    for (auto statement : statements) {
        statement->traverseNestedTerms([&](ITheoryTerm* term) {
            if (auto s = dynamic_cast<SymbolicTerm*>(term)) {
                this->symbolicTerms[s->id] = s;
            }
            else if (auto s = dynamic_cast<ExpressionTerm*>(term)) {
                helper(s);
            }
        });
    }
}

void QF_LIA_logic::getDeclarationStatements(std::ostringstream &output) {
    for (const auto p : this->symbolicTerms) {
        auto term = p.second;
        output << SMT::DeclareConst(term->name, "Int");
    }
}

string QF_LIA_logic::getString(float value) {
    return to_string(static_cast<int>(value));
}

string QF_LIA_logic::getIndividualRealTermAssertionStatement(ITheoryTerm* rightTerm, RealTerm* realTerm) {
    LOG(ERROR) << "Real Term not allowed in LIA logic." << endl;
}

float QF_LIA_logic::getRealTermValue(RealTerm* num) {
    LOG(ERROR) << "Real Term not allowed in LIA logic." << endl;
}

float QF_LIA_logic::solveExpression(ExpressionTerm* expression) {
    string operation = (expression->children.size() == 1) ? expression->operation->name : "+";
    float value = 0;

    for (auto child: expression->children) {
        float termValue = 0;

        if (auto num = dynamic_cast<NumericTerm*>(child)) {
            termValue = num->value;
        }
        else if (auto num = dynamic_cast<RealTerm*>(child)) {
            termValue = getRealTermValue(num);
        }
        else if (auto expression = dynamic_cast<ExpressionTerm*>(child)) {
            termValue = solveExpression(expression);
        }
        else {
            LOG(ERROR) << "Invalid syntax for dom statement." << endl;
        }

        // Apply the operation
        if (operation == "+") {
            value += termValue;
        } 
        else if (operation == "-") {
            value -= termValue;
        } 
        else if (operation == "*") {
            value *= termValue;
        }

        // Update operation for next term
        operation = expression->operation->name;
    }
    return value;
}

float QF_LIA_logic::getTermValue(ITheoryTerm* term) {
    if (auto num = dynamic_cast<NumericTerm*>(term)) {
        return num->value;
    }
    else if (auto num = dynamic_cast<RealTerm*>(term)) {
        return getRealTermValue(num);
    }
    else if (auto exp = dynamic_cast<ExpressionTerm*>(term)) {
        return solveExpression(exp);
    }
    LOG(ERROR) << "Invalid syntax for dom statement." << endl;
}

tuple<float, float> QF_LIA_logic::getLowerAndUpperBounds(ExpressionTerm* domainExpression) {
    ITheoryTerm* lbTerm = domainExpression->children.front();
    ITheoryTerm* ubTerm = domainExpression->children.back();
        
    float lowerBound = getTermValue(lbTerm);
    float upperBound = getTermValue(ubTerm);
    return make_tuple(lowerBound, upperBound);
}

string QF_LIA_logic::getLowerUpperBoundAssertionStatement(ExpressionTerm* domainExpression, ITheoryTerm* rightTerm) {
    auto boundTuple = getLowerAndUpperBounds(domainExpression);
    auto lowerBound = get<0>(boundTuple);
    auto upperBound = get<1>(boundTuple);

    string lowerBoundString = getString(abs(lowerBound));
    string upperBoundString = getString(abs(upperBound));

    if (lowerBound < 0) {
        lowerBoundString = "(- " + lowerBoundString + ")";
    }

    if (upperBound < 0) {
        upperBoundString = "(- " + upperBoundString + ")";
    }

    string expression = " " + SMT::Expr("<=", {
        lowerBoundString,
        SMT::ToString(rightTerm),
        upperBoundString
    });

    return expression;
}

string QF_LIA_logic::getIndividualUnaryAssertionStatement(ExpressionTerm* domainExpression, ITheoryTerm* rightTerm) {
    float value;
    if (auto num = dynamic_cast<NumericTerm*>(domainExpression->children.front())) {
        value = num->value;
    }
    else if (auto num = dynamic_cast<RealTerm*>(domainExpression->children.front())) {
        value = getRealTermValue(num);
    }

    string unaryAssertionStatement = getString(value);
    if (domainExpression->operation->name == "-") {
        unaryAssertionStatement = "(- " + unaryAssertionStatement + ")";
    }

    string expression = " " + SMT::Expr("=", {
        SMT::ToString(rightTerm),
        unaryAssertionStatement
    });

    return expression;
}

string QF_LIA_logic::getIndividualExpressionAssertionStatement(ExpressionTerm* domainExpression, ITheoryTerm* rightTerm) {
    float value = solveExpression(domainExpression);

    string valueString = getString(abs(value));
    if (value < 0) {
        valueString = "(- " + valueString + ")";
    }

    return getIndividualValueAssertionStatement(rightTerm, valueString);
}

string QF_LIA_logic::getIndividualOrLowerUpperBoundAssertionStatement(ExpressionTerm* domainExpression, ITheoryTerm* rightTerm) {
    // for range operation (..) with lower-bound and upper-bound
    if (domainExpression->operation->name == "..") {
        return getLowerUpperBoundAssertionStatement(domainExpression, rightTerm);
    }

    // for individual integer or real values with unary operators 
    else if (
        domainExpression->children.size() == 1
        && (dynamic_cast<NumericTerm*>(domainExpression->children.front())
        || dynamic_cast<RealTerm*>(domainExpression->children.front()))
    ){
        return getIndividualUnaryAssertionStatement(domainExpression, rightTerm);
    }

    // for individual values of expression term, e.g. ((2+3)-1)
    else {
        return getIndividualExpressionAssertionStatement(domainExpression, rightTerm);
    }
}

string QF_LIA_logic::getIndividualValueAssertionStatement(ITheoryTerm* rightTerm, string valueString) {
    string expression = " " + SMT::Expr("=", {
        SMT::ToString(rightTerm),
        valueString
    });
    return expression;
}

string QF_LIA_logic::getDomAssertionStatement(TheoryStatement* statement) {
    string domStatement = "or";
    for (auto singleElement: statement->leftElements){
        // for expression term with individual unary or expression terms and with lower and upper bound inside dom
        if (auto domainExpression = dynamic_cast<ExpressionTerm*>(singleElement->terms.front())) {
            domStatement += getIndividualOrLowerUpperBoundAssertionStatement(domainExpression, statement->rightTerm);
        }

        // for individual integer values inside dom
        else if (auto numericTerm = dynamic_cast<NumericTerm*>(singleElement->terms.front())) {
            string valueString = getString(numericTerm->value);
            domStatement += getIndividualValueAssertionStatement(statement->rightTerm, valueString);
        }

        // for individual real values inside dom
        else if (auto realTerm = dynamic_cast<RealTerm*>(singleElement->terms.front())) {
            domStatement += getIndividualRealTermAssertionStatement(statement->rightTerm, realTerm);
        }
    }

    domStatement = "(" + domStatement + ")";
    return domStatement;
}

string QF_LIA_logic::getSumAssertionStatement(TheoryStatement* statement) {
    list<string> elements;
    for (const auto element : statement->leftElements) {
        elements.push_back(toString(element));
    }
    auto sumOfElements = SMT::Expr("+", elements, true);

    // HACK: SMT-LIB doesn't have a != operator
    string operation = statement->operation->name;
    if (operation == "!=") {
        operation = "distinct";
    }

    auto sumStatement = SMT::Expr(operation, {sumOfElements, SMT::ToString(statement->rightTerm)});
    return sumStatement;
}

void QF_LIA_logic::getAssertionStatements(std::ostringstream &output) {
    for (const auto statement : statements) {
        string assertionStatement;

        if (statement->symbolicTerm->name == "sum")  {
            assertionStatement = getSumAssertionStatement(statement);
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

list<SymbolicTerm*> QF_LIA_logic::getConstraintVariables() {
    list<SymbolicTerm*> variables;
    for (auto pair : symbolicTerms) {
        variables.push_back(pair.second);
    }
    return variables;
}

string QF_LIA_logic::toString(TheoryAtomElement* element) {
    if (element->literals.empty()) {
        list<string> terms;
        for (auto term : element->terms) {
            terms.push_back(SMT::ToString(term));
        }

        return SMT::Expr("+", terms, true);
    }

    LOG(ERROR) << "Not yet supported";
}
