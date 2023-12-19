//
// Created by wzl on 2021/10/12.
//

#ifndef TIGER_COMPILER_X64FRAME_H
#define TIGER_COMPILER_X64FRAME_H

#include "tiger/frame/frame.h"

namespace frame {

const int wordsize = 8;

class X64RegManager : public RegManager {
public:
  X64RegManager() : frame::RegManager() {
    temp_map_->Enter(RAX(), new std::string("%rax"));
    temp_map_->Enter(RDI(), new std::string("%rdi"));
    temp_map_->Enter(RSI(), new std::string("%rsi"));
    temp_map_->Enter(RDX(), new std::string("%rdx"));
    temp_map_->Enter(RCX(), new std::string("%rcx"));
    temp_map_->Enter(R8(), new std::string("%r8"));
    temp_map_->Enter(R9(), new std::string("%r9"));
    temp_map_->Enter(R10(), new std::string("%r10"));
    temp_map_->Enter(R11(), new std::string("%r11"));
    temp_map_->Enter(RBX(), new std::string("%rbx"));
    temp_map_->Enter(RBP(), new std::string("%rbp"));
    temp_map_->Enter(R12(), new std::string("%r12"));
    temp_map_->Enter(R13(), new std::string("%r13"));
    temp_map_->Enter(R14(), new std::string("%r14"));
    temp_map_->Enter(R15(), new std::string("%r15"));
    temp_map_->Enter(RSP(), new std::string("%rsp"));
  };
  temp::TempList* Registers() override;
  temp::TempList* ArgRegs() override;
  temp::TempList* CallerSaves() override;
  temp::TempList* CalleeSaves() override;
  temp::TempList* ReturnSink() override;
  int WordSize() override;
  temp::Temp* FramePointer() override;
  temp::Temp* StackPointer() override;
  temp::Temp* ReturnValue() override;
  
  temp::Temp* GetNthArg(int i);
  temp::Temp* RAX();
  temp::Temp* RDI();
  temp::Temp* RSI();
  temp::Temp* RDX();
  temp::Temp* RCX();
  temp::Temp* R8();
  temp::Temp* R9();
  temp::Temp* R10();
  temp::Temp* R11();
  temp::Temp* RBX();
  temp::Temp* RBP();
  temp::Temp* R12();
  temp::Temp* R13();
  temp::Temp* R14();
  temp::Temp* R15();
  temp::Temp* RSP();
  
  std::vector<std::string> Colors() override;

private:
  temp::Temp *rax, *rdi, *rsi, *rdx, *rcx, *r8, 
            *r9, *r10, *r11, *rbx, *rbp, *r12, 
            *r13, *r14, *r15, *rsp;
};

class InFrameAccess : public Access {
public:
  int offset;

  InFrameAccess(int offset) : Access(INFRAME), offset(offset) { assert(offset < 0); };
  tree::Exp* ToExp(tree::Exp* framPtr) const { 
    return new tree::MemExp(new tree::BinopExp(tree::BinOp::PLUS_OP, framPtr, new tree::ConstExp(offset)));
  };
};

class InRegAccess : public Access {
public:
  temp::Temp* reg;

  InRegAccess(temp::Temp* reg) : Access(INREG), reg(reg) {};
  tree::Exp* ToExp(tree::Exp* framePtr) const { return new tree::TempExp(reg); };
};

class X64Frame : public Frame {
public:
  std::list<tree::Stm *> save_args;

  X64Frame(temp::Label* name, std::list<bool> escapes);
  Access* AllocLocal(bool escape) {
    Access *tmp = nullptr;
    if (escape) {
      tmp = new InFrameAccess(s_offset_);
      s_offset_ -= wordsize;
    } else {
      tmp = new InRegAccess(temp::TempFactory::NewTemp());
    }
    return tmp;
  };
  tree::Stm *ProcEntryExit1(tree::Stm *body) override;
  assem::InstrList *ProcEntryExit2(assem::InstrList *body) override;
  assem::Proc *ProcEntryExit3(assem::InstrList *body) override;
};

} // namespace frame
#endif // TIGER_COMPILER_X64FRAME_H
