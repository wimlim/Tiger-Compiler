#include "tiger/frame/x64frame.h"

extern frame::RegManager *reg_manager;

namespace frame {

X64Frame::X64Frame(temp::Label *name, std::list<bool> escapes) {
  label_ = name;
  formals_ = new AccessList();

  s_offset_ = -8;
  int i = 1;
  int arg_num = escapes.size();
  for (auto it : escapes) {
    Access *a = AllocLocal(it);
    formals_->Append(a);

    if (reg_manager->GetNthArg(i)) {
      save_args.push_back(new tree::MoveStm(a->ToExp(new tree::TempExp(reg_manager->FramePointer())), new tree::TempExp(reg_manager->GetNthArg(i))));
    }
    else {
      save_args.push_back(new tree::MoveStm(a->ToExp(
        new tree::TempExp(reg_manager->FramePointer())), 
        new tree::MemExp(
          new tree::BinopExp(tree::BinOp::PLUS_OP, 
            new tree::TempExp(reg_manager->FramePointer()), 
              new tree::ConstExp((arg_num - i + 2) * frame::wordsize)))));
    }
    ++i;
  }
}

tree::Exp *ExternalCall(std::string s, tree::ExpList *args) {
  return new tree::CallExp(new tree::NameExp(temp::LabelFactory::NamedLabel(s)), args);
}

tree::Stm *X64Frame::ProcEntryExit1(tree::Stm *body) {
  for (auto &it : save_args) {
    body = tree::Stm::Seq(it, body);
  }
  return body;
}

assem::InstrList *X64Frame::ProcEntryExit2(assem::InstrList *body) {
  body->Append(new assem::OperInstr("", NULL, reg_manager->ReturnSink(), NULL));
  return body;
}

assem::Proc *X64Frame::ProcEntryExit3(assem::InstrList *body) {
  static char buf[256];
  std::string prolog;
  std::string epilog;

  sprintf(buf, ".set %s_framesize, %d\n", label_->Name().c_str(), -s_offset_);
  prolog = std::string(buf);

  sprintf(buf, "%s:\n", label_->Name(). c_str());
  prolog.append(std::string(buf));

  sprintf(buf, "subq $%d, %%rsp\n", -s_offset_);
  prolog.append(std::string(buf));

  sprintf(buf, "addq $%d, %%rsp\n", -s_offset_);
  epilog.append(std::string(buf));
  
  epilog.append(std::string("retq\n"));

  return new assem::Proc(prolog, body, epilog);
}


temp::TempList* X64RegManager::Registers() {
  static temp::TempList* templist = NULL;
  
  if (templist) return templist;
  
  templist = new temp::TempList();

  templist->Append(RAX());
  templist->Append(RDI());
  templist->Append(RSI());
  templist->Append(RDX());
  templist->Append(RCX());
  templist->Append(R8());
  templist->Append(R9());
  templist->Append(R10());
  templist->Append(R11());
  templist->Append(RBX());
  templist->Append(RBP());
  templist->Append(R12());
  templist->Append(R13());
  templist->Append(R14());
  templist->Append(R15());
  return templist;
}

temp::TempList* X64RegManager::ArgRegs() {
  static temp::TempList* templist = NULL;

  if (templist) return templist;

  templist = new temp::TempList();
  templist->Append(RDI());
  templist->Append(RSI());
  templist->Append(RDX());
  templist->Append(RCX());
  templist->Append(R8());
  templist->Append(R9());
  return templist;
}

temp::TempList* X64RegManager::CallerSaves() {
  static temp::TempList* templist = NULL;

  if (templist)
    return templist;

  templist = new temp::TempList();
  templist->Append(RAX());
  templist->Append(RDI());
  templist->Append(RSI());
  templist->Append(RDX());
  templist->Append(RCX());
  templist->Append(R8());
  templist->Append(R9());
  templist->Append(R10());
  templist->Append(R11());
  return templist;
}
temp::TempList* X64RegManager::CalleeSaves() {
  static temp::TempList* templist = NULL;

  if (templist)
    return templist;

  templist = new temp::TempList();
  templist->Append(RBX());
  templist->Append(RBP());
  templist->Append(R12());
  templist->Append(R13());
  templist->Append(R14());
  templist->Append(R15());
  return templist; 
}

temp::TempList* X64RegManager::ReturnSink() {
  static temp::TempList* templist = NULL;
  if (templist)
    return templist;
  
  templist = new temp::TempList();
  templist->Append(ReturnValue());
  return templist;
}

int X64RegManager::WordSize() {
  return 8;
}

temp::Temp* X64RegManager::FramePointer() {
  return RBP();
}

temp::Temp* X64RegManager::StackPointer() {
  return RSP();
}

temp::Temp* X64RegManager::ReturnValue() {
  return RAX();
}

temp::Temp* X64RegManager::GetNthArg(int i) {
  switch (i)
  {
    case 1: return RDI();
    case 2: return RSI();
    case 3: return RDX();
    case 4: return RCX();
    case 5: return R8();
    case 6: return R9();
  }
  return NULL;
}

temp::Temp* X64RegManager::RAX() {
  if (rax == nullptr) rax = temp::TempFactory::NewTemp();
  return rax;
}

temp::Temp* X64RegManager::RDI() {
  if (rdi == nullptr) rdi = temp::TempFactory::NewTemp();
  return rdi;
}

temp::Temp* X64RegManager::RSI() {
  if (rsi == nullptr) rsi = temp::TempFactory::NewTemp();
  return rsi;
}

temp::Temp* X64RegManager::RDX() {
  if (rdx == nullptr) rdx = temp::TempFactory::NewTemp();
  return rdx;
}

temp::Temp* X64RegManager::RCX() {
  if (rcx == nullptr) rcx = temp::TempFactory::NewTemp();
  return rcx;
}

temp::Temp* X64RegManager::R8() {
  if (r8 == nullptr) r8 = temp::TempFactory::NewTemp();
  return r8;
}

temp::Temp* X64RegManager::R9() {
  if (r9 == nullptr) r9 = temp::TempFactory::NewTemp();
  return r9;
}

temp::Temp* X64RegManager::R10() {
  if (r10 == nullptr) r10 = temp::TempFactory::NewTemp();
  return r10;
}

temp::Temp* X64RegManager::R11() {
  if (r11 == nullptr) r11 = temp::TempFactory::NewTemp();
  return r11;
}

temp::Temp* X64RegManager::RBX() {
  if (rbx == nullptr) rbx = temp::TempFactory::NewTemp();
  return rbx;
}

temp::Temp* X64RegManager::RBP() {
  if (rbp == nullptr) rbp = temp::TempFactory::NewTemp();
  return rbp;
}

temp::Temp* X64RegManager::R12() {
  if (r12 == nullptr) r12 = temp::TempFactory::NewTemp();
  return r12;
}

temp::Temp* X64RegManager::R13() {
  if (r13 == nullptr) r13 = temp::TempFactory::NewTemp();
  return r13;
}

temp::Temp* X64RegManager::R14() {
  if (r14 == nullptr) r14 = temp::TempFactory::NewTemp();
  return r14;
}

temp::Temp* X64RegManager::R15() {
  if (r15 == nullptr) r15 = temp::TempFactory::NewTemp();
  return r15;
}

temp::Temp* X64RegManager::RSP() {
  if (rsp == nullptr) rsp = temp::TempFactory::NewTemp();
  return rsp;
}
  

std::vector<std::string> X64RegManager::Colors() {
  std::vector<std::string> res;
  res.push_back("%rax");
  res.push_back("%rdi");
  res.push_back("%rsi");
  res.push_back("%rdx");
  res.push_back("%rcx");
  res.push_back("%r8");
  res.push_back("%r9");
  res.push_back("%r10");
  res.push_back("%r11");
  res.push_back("%rbx");
  res.push_back("%rbp");
  res.push_back("%r12");
  res.push_back("%r13");
  res.push_back("%r14");
  res.push_back("%r15");
  return res;
}

} // namespace frame
