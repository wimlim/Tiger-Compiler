#include "tiger/frame/x64frame.h"
#include <sstream>

extern frame::RegManager *reg_manager;

namespace frame {
Access* X64Frame::allocLocal(bool escape) {
  if (escape) {
    return new InFrameAccess(s_offset_ -= wordsize);
  } else {
    return new InRegAccess(temp::TempFactory::NewTemp());
  }
}


tree::Exp* externalCall(std::string s, tree::ExpList* args) {
  return new tree::CallExp(new tree::NameExp(temp::LabelFactory::NamedLabel(s)), args);
};

tree::Stm* procEntryExit1(Frame* frame, tree::Stm* stm) {
  tree::Stm* viewshift = new tree::ExpStm(new tree::ConstExp(0));

  int num = 1;
  for (auto ele : frame->formals_->GetList()) {
    if (reg_manager->GetNthReg(num)) {
      viewshift = new tree::SeqStm(
        viewshift, 
        new tree::MoveStm(
          ele->ToExp(new tree::TempExp(reg_manager->FramePointer())),
          new tree::TempExp(reg_manager->GetNthArg(num))
        )
      );
    }
    num++;
  }

  return new tree::SeqStm(viewshift, stm);
}


assem::InstrList* procEntryExit2(assem::InstrList* body) {
  return body;
}


assem::Proc* procEntryExit3(frame::Frame* frame, assem::InstrList* body) {
  std::ostringstream prolog;
  prolog << ".set " << frame->label_->Name() << "_framesize, " << -frame->s_offset_ << "\n";
  prolog << frame->label_->Name() << ":\n";
  prolog << "\tsubq $" << frame->label_->Name() << "_framesize, %rsp\n";

  std::ostringstream epilog;
  epilog << "\taddq $" << frame->label_->Name() << "_framesize, %rsp\n";
  epilog << "\tret\n";

  return new assem::Proc(prolog.str(), body, epilog.str());
}


temp::TempList* X64RegManager::Registers() {
  static temp::TempList* templist = NULL;
  
  if (templist) return templist;
  
  templist = new temp::TempList();

  templist->Append(rax);
  templist->Append(rdi);
  templist->Append(rsi);
  templist->Append(rdx);
  templist->Append(rcx);
  templist->Append(r8);
  templist->Append(r9);
  templist->Append(r10);
  templist->Append(r11);
  templist->Append(rbx);
  templist->Append(rbp);
  templist->Append(r12);
  templist->Append(r13);
  templist->Append(r14);
  templist->Append(r15);
  return templist;
}

temp::TempList* X64RegManager::ArgRegs() {
  static temp::TempList* templist = NULL;

  if (templist) return templist;

  templist = new temp::TempList();
  templist->Append(rdi);
  templist->Append(rsi);
  templist->Append(rdx);
  templist->Append(rcx);
  templist->Append(r8);
  templist->Append(r9);
  return templist;
}

temp::TempList* X64RegManager::CallerSaves() {
  static temp::TempList* templist = NULL;

  if (templist) return templist;

  templist = new temp::TempList();
  templist->Append(rax);
  templist->Append(rdi);
  templist->Append(rsi);
  templist->Append(rdx);
  templist->Append(rcx);
  templist->Append(r8);
  templist->Append(r9);
  templist->Append(r10);
  templist->Append(r11);
  return templist;
}

temp::TempList* X64RegManager::CalleeSaves() {
  static temp::TempList* templist = NULL;

  if (templist) return templist;

  templist = new temp::TempList();
  templist->Append(rbx);
  templist->Append(rbp);
  templist->Append(r12);
  templist->Append(r13);
  templist->Append(r14);
  templist->Append(r15);
  return templist; 
}

temp::TempList* X64RegManager::ReturnSink() {
  return NULL;
}

int X64RegManager::WordSize() {
  return 8;
}

temp::Temp* X64RegManager::FramePointer() {
  return rbp;
}

temp::Temp* X64RegManager::StackPointer() {
  return rsp;
}

temp::Temp* X64RegManager::ReturnValue() {
  return rax;
}

temp::Temp* X64RegManager::GetNthReg(int i) {
  static temp::Temp* regs[] = {rax, rdi, rsi, rdx, rcx, r8, r9, r10, r11, rbx, rbp, r12, r13, r14, r15, rsp};
  if (i >= 1 && i <= 16) {
    return regs[i - 1];
  } else {
    return NULL;
  }
}


temp::Temp* X64RegManager::GetNthArg(int i) {
  static temp::Temp* args[] = {rdi, rsi, rdx, rcx, r8, r9};
  if (i >= 1 && i <= 6) {
    return args[i - 1];
  } else {
    return NULL;
  }
}

} // namespace frame
