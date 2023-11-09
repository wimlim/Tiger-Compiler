#include "straightline/slp.h"

#include <iostream>

namespace A {
int A::CompoundStm::MaxArgs() const {
  // TODO: put your code here (lab1).
  int maxArgs1 = stm1->MaxArgs();
  int maxArgs2 = stm2->MaxArgs();
  return maxArgs1 > maxArgs2 ? maxArgs1 : maxArgs2;
}

Table *A::CompoundStm::Interp(Table *t) const {
  // TODO: put your code here (lab1).
  return stm2->Interp(stm1->Interp(t));
}

int A::AssignStm::MaxArgs() const {
  // TODO: put your code here (lab1).
  return exp->MaxArgs();
}

Table *A::AssignStm::Interp(Table *t) const {
  // TODO: put your code here (lab1).
  IntAndTable *intAndTable = exp->Interp(t);
  return intAndTable->t->Update(id, intAndTable->i);
}

int A::PrintStm::MaxArgs() const {
  // TODO: put your code here (lab1).
  return exps->MaxArgs();
}

Table *A::PrintStm::Interp(Table *t) const {
  // TODO: put your code here (lab1).
  IntAndTable *intAndTable = exps->Interp(t);
  return intAndTable->t;
}


int Table::Lookup(const std::string &key) const {
  if (id == key) {
    return value;
  } else if (tail != nullptr) {
    return tail->Lookup(key);
  } else {
    assert(false);
  }
}

Table *Table::Update(const std::string &key, int val) const {
  return new Table(key, val, this);
}

int IdExp::MaxArgs() const {
  return 1;
}

IntAndTable* IdExp::Interp(Table *t) const {
  return new IntAndTable(t->Lookup(id), t);
}

int NumExp::MaxArgs() const {
  return 1;
}

IntAndTable* NumExp::Interp(Table *t) const {
  return new IntAndTable(num, t);
}

int OpExp::MaxArgs() const {
  return 1;
}

IntAndTable * OpExp::Interp(Table* t) const {
  IntAndTable *leftTable = left->Interp(t);
  IntAndTable *rightTable = right->Interp(leftTable->t);

  int result;
  switch (oper) {
    case PLUS:
      result = leftTable->i + rightTable->i;
      break;
    case MINUS:
      result = leftTable->i - rightTable->i;
      break;
    case TIMES:
      result = leftTable->i * rightTable->i;
      break;
    case DIV:
      result = leftTable->i / rightTable->i;
      break;
    default:
      assert(false);
  }
  return new IntAndTable(result, rightTable->t);
}

int EseqExp::MaxArgs() const {
  int maxArgs1 = stm->MaxArgs();
  int maxArgs2 = exp->MaxArgs();
  return maxArgs1 > maxArgs2 ? maxArgs1 : maxArgs2;
}

IntAndTable* EseqExp::Interp(Table *t) const {
  return exp->Interp(stm->Interp(t));
}

int PairExpList::MaxArgs() const {
  return exp->MaxArgs() + tail->MaxArgs();
}

int PairExpList::NumExps() const {
  return 1 + tail->NumExps();
}

IntAndTable* PairExpList::Interp(Table *t) const {
  IntAndTable *intAndTable = exp->Interp(t);
  std::cout << intAndTable->i << " ";
  return tail->Interp(intAndTable->t);
}

int LastExpList::MaxArgs() const {
  return exp->MaxArgs();
}

int LastExpList::NumExps() const {
  return 1;
}

IntAndTable* LastExpList::Interp(Table *t) const {
  IntAndTable *intAndTable = exp->Interp(t);
  std::cout << intAndTable->i << std::endl;
  return intAndTable;
}

}  // namespace A
