/*
 * File read.cc
 * Last modified on 2 19:34 2002
 * By Yuliya Babovich
 *
 */

// Copyright 1998 by Patrik Simons
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either version 2
// of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.
//
// Patrik.Simons@hut.fi
#include "read.h"
#include "atomrule.h"
#include "defines.h"
#include "program.h"
#include "theory.h"
#include <cstdlib>
#include <exception>
#include <float.h>
#include <fstream>
#include <glog/logging.h>
#include <iostream>
#include <limits.h>
#include <list>
#include <map>
#include <numeric>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <string.h>
#include <string>
#include <boost/algorithm/string.hpp>
#include <filesystem>

using namespace boost::algorithm;

Read::Read(Program *p, Api *a, Param *params) : program(p), api(a), params(params) {
  // atoms = 0;
  size = 0;
  models = 1;
  mValues[-1] = 1;
}

//
// creates an instance of a new atom
//
// FIXME Why doesn't the API do this check instead?
Atom *Read::getOrCreateAtom(long n) {
  if (atoms[n] == 0)
    atoms[n] = api->new_atom(n);
  return atoms[n];
}

Atom *Read::getAtomFromLiteral(long n) { return getOrCreateAtom(abs(n)); }

enum StatementType {
  END = 0,
  RULE = 1,
  MINIMIZE = 2,
  PROJECT = 3,    // NOTE Not supported
  OUTPUT = 4,
  EXTERNAL = 5,   // NOTE Not supported
  ASSUMPTION = 6, // NOTE Not supported
  HEURISTIC = 7,  // NOTE Not supported
  EDGE = 8,       // NOTE Not supported
  THEORY = 9,
  COMMENT = 10
};

enum HeadType {
  // x :- y.
  // x|y :- z.
  DISJUNCTION = 0,
  // { x } :- y.
  CHOICE = 1
};

enum BodyType { NORMAL_BODY = 0, WEIGHT_BODY = 1 };

void Read::readRuleLine(istringstream &line) {
  int headType, headLength;
  line >> headType >> headLength;

  if (headType == DISJUNCTION) {
    api->begin_rule(BASICRULE);
  } else if (headType == CHOICE) {
    api->begin_rule(CHOICERULE);
  }

  if (headType == DISJUNCTION && headLength > 1) {
    LOG(ERROR) << "Disjunction rules with more than one head atom are not supported. Line: " + line.str();
  }

  for (int i = 0; i < headLength; i++) {
    long literal;
    line >> literal;

    Atom *a = getAtomFromLiteral(literal);
    api->add_head_repetition(a);
  }

  if (headLength == 0) {
    Atom *neverAtom = getOrCreateAtom(0);
    api->set_name(neverAtom, NEVER_ATOM.c_str());
    api->set_compute(neverAtom, false);

    program->false_atom = neverAtom;

    api->add_head_repetition(neverAtom);

    // FIXME setting type to constraint rule seems to break things
    // api->type = CONSTRAINTRULE;
  }

  int bodyType;
  line >> bodyType;

  if (bodyType == NORMAL_BODY) {
    int bodyLength;
    line >> bodyLength;
    for (int i = 0; i < bodyLength; i++) {
      long literal;
      line >> literal;

      Atom *a = getAtomFromLiteral(literal);

      // FIXME How important is the repetition variant?
      // Shouldn't gringo handle this?
      api->add_body(a, literal > 0);
      // api->add_body_repetition(a, literal > 0, api->type);
    }
  } else if (bodyType == WEIGHT_BODY) {
    Weight lowerBound;
    int numOfLiterals;
    line >> lowerBound >> numOfLiterals;

    api->type = WEIGHTRULE;
    api->set_atleast_weight(lowerBound);

    for (int i = 0; i < numOfLiterals; i++) {
      long literal;
      Weight weight;
      line >> literal >> weight;

      Atom *a = getAtomFromLiteral(literal);
      api->add_body(a, literal > 0, weight);
    }
  } else {
    throw runtime_error("Unsupported body type. Line: " + line.str());
  }

  api->end_rule();
}

void Read::readOutputLine(istringstream &line) {
  int _;
  int numOfLiterals;
  string atomName;
  long atomId;
  line >> _ >> atomName >> numOfLiterals >> atomId;

  if (numOfLiterals == 0) {
    auto atom = api->new_atom();
    api->set_name(atom, atomName.c_str());
    api->set_compute(atom, true);
    atom->showInOutputAnswerSet = true;

    api->begin_rule(BASICRULE);
    api->add_head(atom);
    api->end_rule();

  } else if (numOfLiterals == 1) {
    Atom *a = getOrCreateAtom(atomId);
    api->set_name(a, atomName.c_str());
    a->showInOutputAnswerSet = true;
  } else if (numOfLiterals > 1) {
    throw runtime_error(
        "Output line with multiple literals not implemented yet. Line: " +
        line.str());
  }
}

enum TheoryLineType {
  NUMERIC_TERMS = 0,
  SYMBOLIC_TERMS = 1,
  COMPOUND_TERMS = 2,
  ATOM_ELEMENTS = 4,
  DIRECTIVE = 5,
  STATEMENT = 6
};

// TODO support directives
void Read::readTheoryStatements(list<string> &lines) {
  for (string line : lines) {
    stringstream lineStream(line);
    int statementType, theoryLineType;
    lineStream >> statementType;

    if (statementType == THEORY) {
      lineStream >> theoryLineType;

      if (theoryLineType == STATEMENT) {
        int atomId;
        lineStream >> atomId;
        Atom *atom = getOrCreateAtom(atomId);
        atom->theoryStatement = true;

        // treat all theory statement atoms as a choice rule atom
        string choiceRuleLine = "1 1 " + to_string(atomId) + " 0 0";
        unique_ptr<istringstream> choiceRulelineStream(new istringstream(choiceRuleLine));
        readRuleLine(*choiceRulelineStream);

        stringstream name;
        name << THEORY_ATOM_PREFIX << "(" << atomId << ")";
        api->set_name(atom, name.str().c_str());

        int symbolicTermId;
        lineStream >> symbolicTermId;
        auto symbolicTerm = dynamic_cast<SymbolicTerm*>(program->theoryTerms[symbolicTermId]);
        if (symbolicTerm == nullptr) {
          LOG(ERROR) << "Could not find symbolic theory term " << symbolicTermId << " referenced by line '" << line << "'";
        }

        int numOfElements;
        lineStream >> numOfElements;
        list<TheoryAtomElement *> leftElements;
        for (int i = 0; i < numOfElements; i++) {
          int theoryAtomElementId;
          lineStream >> theoryAtomElementId;
          auto element = program->theoryAtomElements[theoryAtomElementId];
          if (element == nullptr) {
            LOG(ERROR) << "Could not find theory atom element " << theoryAtomElementId << " referenced by line '" << line << "'";
          }
          leftElements.push_back(element);
        }

        int operatorTermId;
        lineStream >> operatorTermId;
        auto operatorTerm = dynamic_cast<SymbolicTerm*>(program->theoryTerms[operatorTermId]);
        if (operatorTerm == nullptr) {
          LOG(ERROR) << "Could not find operator theory term " << operatorTermId << " referenced by line '" << line << "'";
        }

        int rightTermId;
        lineStream >> rightTermId;
        auto rightTerm = program->theoryTerms[rightTermId];
        if (rightTerm == nullptr) {
          LOG(ERROR) << "Could not find right theory term " << rightTermId << " referenced by line '" << line << "'";
        }

        // for type specification statements
        if (symbolicTerm->name == "type") {
          if (params->logic == 2) {
            saveTypes(leftElements, rightTerm);
          }
          else {
            LOG(WARNING) << "LIRA logic required for type specification!! Ignoring type specifications..." << endl;
          }
          continue;
        }

        auto statement = new TheoryStatement(atom, symbolicTerm, leftElements, operatorTerm, rightTerm);
        program->theoryStatements[atomId] = statement;
      }
    }
  }
}

void Read::saveTypes(list<TheoryAtomElement*> leftElements, ITheoryTerm* rightTerm) {
  string variableType;
  if (auto type = dynamic_cast<SymbolicTerm*>(rightTerm)){
    variableType = type->name;
    transform(variableType.begin(), variableType.end(), variableType.begin(), ::tolower);
  }
  else {
    LOG(ERROR) << "Only variables types such as 'int' and 'real' are allowed for type specifications." << endl;
  }

  for (auto element: leftElements) {
    if (element->terms.size() > 1) {
      LOG(ERROR) << "Please use ';' instead of ',' to separate variables in type specifications." << endl;
    }
    
    auto term = element->terms.front();
    if (auto variable = dynamic_cast<SymbolicTerm*>(term)) {
      program->typeMap[variable->name] = variableType;
    }
    else {
      LOG(ERROR) << "Only variable names are allowed inside type specifications." << endl;
    }
  }
}

void Read::readTheoryTerms(list<string> &lines) {
  for (string line : lines) {
    stringstream lineStream(line);
    int statementType;
    lineStream >> statementType;

    if (statementType == THEORY) {
      int theoryLineType, termId;
      lineStream >> theoryLineType >> termId;

      switch (theoryLineType) {
        case NUMERIC_TERMS:
          int termValue;
          lineStream >> termValue;
          program->theoryTerms[termId] = new NumericTerm(termId, termValue);
          break;
        case SYMBOLIC_TERMS: {
          int length;
          string symbolValue;
          lineStream >> length >> symbolValue;
          if (params->logic == 1 || params->logic == 2) {
            try {
              string floatString = trim_copy_if(symbolValue, is_any_of("\"\'"));
              float floatValue = stof(floatString);
              program->theoryTerms[termId] = new RealTerm(termId, floatValue);
            }
            catch (...) {
              program->theoryTerms[termId] = new SymbolicTerm(termId, symbolValue);
            }
          } else {
            program->theoryTerms[termId] = new SymbolicTerm(termId, symbolValue);
          }
          break;
        }
        case COMPOUND_TERMS:
          int t, numOfTerms;
          lineStream >> t >> numOfTerms;

          if (t < 0) {
            auto tupleTerm = new TupleTerm(termId, (TupleType)t);
            for (int i = 0; i < numOfTerms; i++) {
              int childTermId;
              lineStream >> childTermId;
              auto childTerm = program->theoryTerms[childTermId];
              if (childTerm == nullptr) {
                LOG(ERROR) << "Could not find child theory term " << childTermId << " referenced by line '" << line << "'";
              }
              tupleTerm->children.push_back(childTerm);
            }
            program->theoryTerms[termId] = tupleTerm;
          } else {
            auto operationTerm = dynamic_cast<SymbolicTerm*>(program->theoryTerms[t]);
            if (operationTerm == nullptr) {
              LOG(ERROR) << "Could not find symbolic operator theory term " << operationTerm << " referenced by line '" << line << "'";
            }

            list<ITheoryTerm*> childTerms;
            for (int i = 0; i < numOfTerms; i++) {
              int childTermId;
              lineStream >> childTermId;
              auto childTerm = program->theoryTerms[childTermId];
              if (childTerm == nullptr) {
                LOG(ERROR) << "Could not find child theory term " << childTermId << " referenced by line '" << line << "'";
              }
              childTerms.push_back(childTerm);
            }

            ITheoryTerm* newTerm;

            bool isValidSymbolName = regex_match(operationTerm->name, regex("^[A-z_]+$"));
            if (isValidSymbolName) {
              ostringstream symbolName;
              symbolName << operationTerm->name;
              symbolName << "(";
              int length = 0;
              int childTermsLength = childTerms.size();
              for (auto child : childTerms) {
                if (auto symbolicTerm = dynamic_cast<SymbolicTerm*>(child)) {
                  symbolName << symbolicTerm->name;
                } else if (auto numericTerm = dynamic_cast<NumericTerm*>(child)) {
                  symbolName << numericTerm->value;
                } else {
                  LOG(ERROR) << "Constraint variables can only contain numeric or symbolic terms. Line: " << line;
                }

                // if (child != childTerms.back()) {
                //   symbolName << ",";
                // }

                if (length < childTermsLength - 1) {
                  symbolName << ",";
                  length += 1;
                }
              }
              symbolName << ")";
              newTerm = new SymbolicTerm(termId, symbolName.str());
            } else {
              auto expressionTerm = new ExpressionTerm(termId, operationTerm);
              expressionTerm->children = childTerms;
              newTerm = expressionTerm;
            }

            program->theoryTerms[termId] = newTerm;
          }
          break;
      }
    }
  }
}

void Read::readTheoryAtomElements(list<string> &lines) {
  for (string line : lines) {
    stringstream lineStream(line);
    int statementType;
    lineStream >> statementType;

    if (statementType == THEORY) {
      int theoryLineType, theoryAtomElementId;
      lineStream >> theoryLineType >> theoryAtomElementId;

      if (theoryLineType == ATOM_ELEMENTS) {
        auto theoryAtomElements = new TheoryAtomElement(theoryAtomElementId);

        int numOfTerms;
        lineStream >> numOfTerms;
        for (int i = 0; i < numOfTerms; i++) {
          int termId;
          lineStream >> termId;
          auto theoryTerm = program->theoryTerms[termId];
          if (theoryTerm == nullptr) {
            LOG(ERROR) << "Could not find definition for theory term " << termId << " referenced in '" << line << "'";
          }

          theoryAtomElements->terms.push_back(theoryTerm);
        }

        int numOfLiterals;
        lineStream >> numOfLiterals;
        for (int i = 0; i < numOfLiterals; i++) {
          int literal;
          lineStream >> literal;
          int atomId = abs(literal);
          auto atom = atoms[atomId];
          if (atom == nullptr) {
            LOG(ERROR) << "Could not find definition for atom " << atomId << " referenced in '" << line << "'";
          }

          theoryAtomElements->literals.push_back(AtomLiteral(atom, literal >= 0));
        }

        program->theoryAtomElements[theoryAtomElementId] = theoryAtomElements;
      }
    }
  }
}

void Read::readMinimizeLine(istringstream &line, int minimizationStatementId) {
  if (params->answerSetsToEnumerate == 1) {
    LOG(WARNING) << "Minimization statements are ignored when only one answer set is generated. Try using the -e flag.";
  }

  int priority, numOfLiterals;
  line >> priority >> numOfLiterals;

  int literal, weight;
  list<int> weights;
  list<tuple<int, int, Atom*>> literalWeights;
  for (int i = 0; i < numOfLiterals; i++) {
    line >> literal >> weight;
    weights.push_back(weight);
    Atom *a = getAtomFromLiteral(literal);
    tuple<int, int, Atom*> lw(literal, weight, a);
    literalWeights.push_back(lw);
  }

  program->lwCollections.push_front(literalWeights);

  int weightsSum = accumulate(weights.begin(), weights.end(), 0.0);
  mValues[priority] = 1 + weightsSum < 0 ? -(weightsSum) : weightsSum;
  // cout << "mValues[" << priority << "]: " << mValues[priority] << endl;
  fValues[priority] = 1;
  for (auto m: mValues) {
    if (m.first < priority) {
      // cout << "m.second: " << m.second << endl;
      fValues[priority] *= m.second;
    } 
  }

  // cout << "fValues[" << priority << "]: " << fValues[priority] << endl;
  
  int normalized_priority = 0;
  auto minimizationStatement = new MinimizationStatement(minimizationStatementId, normalized_priority);
  size_t len_minimizations = program->minimizations.size();
  
  if (len_minimizations > 0) {
    minimizationStatement = program->minimizations.front();
  }

  for (auto lw: literalWeights) {
    literal = get<0>(lw);
    weight = get<1>(lw) * fValues[priority];

  // if (priority != 0) {
  //   LOG(WARNING) << "Minimization statements with non-zero priorities are not supported. Ignoring minimization statement with priority " << priority;
  // }

  // auto minimizationStatement = new MinimizationStatement(minimizationStatementId, priority);

  // for (int i = 0; i < numOfLiterals; i++) {
  //   int literal, weight;
  //   line >> literal >> weight;

    auto atom = getAtomFromLiteral(literal);
    minimizationStatement->atoms.push_back(new MinimizationAtom(*atom, weight));
  }
  if (len_minimizations <= 0) {
    program->minimizations.push_back(minimizationStatement);
  }
}

int Read::read(string fileName) {
  int lineNumber = 0;
  list<string> lines;

  try {
    VLOG(2) << "Opening file: " << fileName;
    ifstream fileStream(fileName);

    string line;
    int minimizationStatementId = 0;
    while (getline(fileStream, line)) {
      VLOG(3) << "Reading line: " << line;
      lineNumber++;
      lines.push_back(line);
      unique_ptr<istringstream> lineStream(new istringstream(line));

      int statementType;
      *lineStream >> statementType;

      switch (statementType) {
      case COMMENT:
      case END:
        break;
      case RULE:
        readRuleLine(*lineStream);
        break;
      case MINIMIZE:
        readMinimizeLine(*lineStream, minimizationStatementId);
        minimizationStatementId++;
        break;
      case OUTPUT:
        readOutputLine(*lineStream);
        break;
      case THEORY:
        // Handled out of sequence below
        break;
      default:
        LOG(WARNING) << "Encountered unknown statement type: " << statementType
                     << ", skipping.";
        break;
      }
    }
  } catch (exception e) {
    LOG(ERROR) << "Failed to parse grounded logic program."
               << " Stopped at " << fileName << ":" << lineNumber
               << " Got exception message: " << e.what();
  }

  VLOG(2) << "Reading theory components";

  readTheoryTerms(lines);
  readTheoryAtomElements(lines);
  readTheoryStatements(lines);

  VLOG(2) << "Done reading";

  if (std::filesystem::exists(fileName)) {
    string delCommand = "rm " + fileName;
    system(delCommand.c_str());
  }

  return 0;
};
