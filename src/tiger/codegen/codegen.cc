#include "tiger/codegen/codegen.h"

#include <cassert>
#include <sstream>

extern frame::RegManager *reg_manager;

namespace {

constexpr int maxlen = 1024;


} // namespace

namespace cg {

void CodeGen::PushReg(assem::InstrList &instr_list, temp::Temp *pos, temp::Temp *to_be_push) {
  frame_->s_offset_ -= frame::wordsize;
  instr_list.Append(new assem::OperInstr("subq $" + std::to_string(frame::wordsize) + ", `d0", new temp::TempList(pos), nullptr, nullptr));
  instr_list.Append(new assem::OperInstr("movq `s0, (`d0)", new temp::TempList(pos), new temp::TempList(to_be_push), nullptr));
}

void CodeGen::PopReg(assem::InstrList &instr_list, temp::Temp *pos, temp::Temp *to_be_pop) {
  instr_list.Append(new assem::OperInstr("subq $" + std::to_string(frame::wordsize) + ", `d0", new temp::TempList(pos), nullptr, nullptr));
  instr_list.Append(new assem::OperInstr("movq (`s0), `d0", new temp::TempList(to_be_pop), new temp::TempList(pos), nullptr));
}

void CodeGen::SaveCalleeRegs(assem::InstrList &instr_list, std::string_view fs) {
  auto new_temp = reg_manager->RAX();
  instr_list.Append(new assem::OperInstr("leaq " + frame_->label_->Name() + "_framesize(%rsp), `d0", new temp::TempList(new_temp), nullptr, nullptr));
  instr_list.Append(new assem::OperInstr("addq $" + std::to_string(frame_->s_offset_) + ", `d0", new temp::TempList(new_temp), nullptr, nullptr));

  PushReg(instr_list, new_temp, reg_manager->R12());
  PushReg(instr_list, new_temp, reg_manager->R13());
  PushReg(instr_list, new_temp, reg_manager->R14());
  PushReg(instr_list, new_temp, reg_manager->R15());
  PushReg(instr_list, new_temp, reg_manager->RBP());
  PushReg(instr_list, new_temp, reg_manager->RBX());
  return;
}

void CodeGen::RestoreCalleeRegs(assem::InstrList &instr_list, std::string_view fs) {
  auto new_temp = reg_manager->RBX();
  instr_list.Append(new assem::OperInstr("leaq " + frame_->label_->Name() + "_framesize(%rsp), `d0", new temp::TempList(new_temp), nullptr, nullptr));
  instr_list.Append(new assem::OperInstr("addq $" + std::to_string(frame_->s_offset_ + 6 * frame::wordsize) + ", `d0", new temp::TempList(new_temp), nullptr, nullptr));

  PopReg(instr_list, new_temp, reg_manager->R12());
  PopReg(instr_list, new_temp, reg_manager->R13());
  PopReg(instr_list, new_temp, reg_manager->R14());
  PopReg(instr_list, new_temp, reg_manager->R15());
  PopReg(instr_list, new_temp, reg_manager->RBP());
  PopReg(instr_list, new_temp, reg_manager->RBX());
  return;
}

void CodeGen::Codegen() {
  fs_ = frame_->label_->Name();
  auto instr_list = new assem::InstrList();

  SaveCalleeRegs(*instr_list, fs_);
  instr_list->Append(new assem::OperInstr("", reg_manager->ArgRegs(), nullptr, nullptr));
  for (auto &it : traces_->GetStmList()->GetList()) {
    it->Munch(*instr_list, fs_);
  }
  RestoreCalleeRegs(*instr_list, fs_);

  assem_instr_ = std::make_unique<AssemInstr> (instr_list);
  frame_->ProcEntryExit2(assem_instr_.get()->GetInstrList());
}

void AssemInstr::Print(FILE *out, temp::Map *map) const {
  for (auto instr : instr_list_->GetList())
    instr->Print(out, map);
  fprintf(out, "\n");
}
} // namespace cg

namespace tree {
/* TODO: Put your lab5 code here */

void SeqStm::Munch(assem::InstrList &instr_list, std::string_view fs) {
  left_->Munch(instr_list, fs);
  right_->Munch(instr_list, fs);
}

void LabelStm::Munch(assem::InstrList &instr_list, std::string_view fs) {
  instr_list.Append(new assem::LabelInstr(temp::LabelFactory::LabelString(label_), label_));
}

void JumpStm::Munch(assem::InstrList &instr_list, std::string_view fs) {
  instr_list.Append(new assem::OperInstr(std::string("jmp `j0"), nullptr, nullptr, new assem::Targets(jumps_)));
}

void CjumpStm::Munch(assem::InstrList &instr_list, std::string_view fs) {
  auto left = left_->Munch(instr_list, fs);
  auto right = right_->Munch(instr_list, fs);
  auto tempList = new temp::TempList();
  tempList->Append(left);
  tempList->Append(right);

  std::string str = "";
  switch(op_){
    case EQ_OP: 
      str = std::string("je ");  
      break;
    case NE_OP: 
      str = std::string("jne "); 
      break;
    case LT_OP: 
      str = std::string("jl ");  
      break;
    case GT_OP: 
      str = std::string("jg ");  
      break;
    case LE_OP: 
      str = std::string("jle "); 
      break;
    case GE_OP: 
      str = std::string("jge "); 
      break;
  }

  auto labelList = new std::vector<temp::Label *>();
  labelList->push_back(true_label_);
  instr_list.Append(new assem::OperInstr("cmpq `s0, `s1", nullptr, new temp::TempList({right, left}), nullptr));
  instr_list.Append(new assem::OperInstr(str + "`j0", nullptr, nullptr, new assem::Targets(labelList)));
}

void MoveStm::Munch(assem::InstrList &instr_list, std::string_view fs) {
  if (dst_->kind_ == Exp::TEMP) {
    auto src = src_->Munch(instr_list, fs);
    auto dst = ((TempExp*) dst_)->temp_;
    instr_list.Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(dst), new temp::TempList(src)));
  }
  else if(dst_->kind_ == Exp::MEM) {
    auto left = src_->Munch(instr_list, fs);
    auto right = ((MemExp *)dst_)->exp_->Munch(instr_list, fs);
    instr_list.Append(new assem::OperInstr("movq `s0, (`s1)", nullptr, new temp::TempList({left, right}), nullptr));
  }
}

void ExpStm::Munch(assem::InstrList &instr_list, std::string_view fs) {
  exp_->Munch(instr_list, fs);
}

temp::Temp *BinopExp::Munch(assem::InstrList &instr_list, std::string_view fs) {
  /* TODO: Put your lab5 code here */
  temp::Temp *new_reg = temp::TempFactory::NewTemp();
  temp::Temp *left;
  temp::Temp *right;
  temp::Label *label_false = temp::LabelFactory::NewLabel();
  temp::Label *label_end = temp::LabelFactory::NewLabel();
  switch (op_){
    case PLUS_OP: case OR_OP:
      left = left_->Munch(instr_list, fs);
      right = right_->Munch(instr_list, fs);
      instr_list.Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(new_reg), new temp::TempList(left)));
      instr_list.Append(new assem::OperInstr("addq `s0, `d0", new temp::TempList(new_reg), new temp::TempList(right), nullptr));
      break;

    case MINUS_OP:
      left = left_->Munch(instr_list, fs);
      right = right_->Munch(instr_list, fs);
      instr_list.Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(new_reg), new temp::TempList(left)));
      instr_list.Append(new assem::OperInstr("subq `s0, `d0", new temp::TempList(new_reg), new temp::TempList(right), nullptr));
      break;

    case MUL_OP: case AND_OP:
      left = left_->Munch(instr_list, fs);
      right = right_->Munch(instr_list, fs);
      instr_list.Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(reg_manager->RAX()), new temp::TempList(left)));
      instr_list.Append(new assem::OperInstr("imulq `s0", new temp::TempList({reg_manager->RAX(), reg_manager->RDX()}), new temp::TempList(right), nullptr));
      instr_list.Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(new_reg), new temp::TempList(reg_manager->RAX())));
      break;

    case DIV_OP:
      left = left_->Munch(instr_list, fs);
      right = right_->Munch(instr_list, fs);
      instr_list.Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(reg_manager->RAX()), new temp::TempList(left)));
      instr_list.Append(new assem::OperInstr("cqto", new temp::TempList(reg_manager->RDX()), new temp::TempList(reg_manager->RAX()), nullptr));
      instr_list.Append(new assem::OperInstr("idivq `s0", new temp::TempList({reg_manager->RAX(), reg_manager->RDX()}), new temp::TempList(right), nullptr));
      instr_list.Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(new_reg), new temp::TempList(reg_manager->RAX())));
      break;
    // case AND_OP:
    //   left = left_->Munch(instr_list, fs);
    //   right = right_->Munch(instr_list, fs);
    //   label_false = temp::LabelFactory::NewLabel();
    //   label_end = temp::LabelFactory::NewLabel();
    //   instr_list.Append(new assem::OperInstr("cmpq $0, `s0", nullptr, new temp::TempList(left), nullptr));
    //   instr_list.Append(new assem::OperInstr("je " + temp::LabelFactory::LabelString(label_false), nullptr, nullptr, nullptr));
    //   instr_list.Append(new assem::OperInstr("cmpq $0, `s0", nullptr, new temp::TempList(right), nullptr));
    //   instr_list.Append(new assem::OperInstr("je " + temp::LabelFactory::LabelString(label_false), nullptr, nullptr, nullptr));
    //   instr_list.Append(new assem::MoveInstr("movq $1, `d0", new temp::TempList(new_reg), nullptr));
    //   instr_list.Append(new assem::OperInstr("jmp " + temp::LabelFactory::LabelString(label_end), nullptr, nullptr, nullptr));
    //   instr_list.Append(new assem::LabelInstr(temp::LabelFactory::LabelString(label_false), label_false));
    //   instr_list.Append(new assem::MoveInstr("movq $0, `d0", new temp::TempList(new_reg), nullptr));
    //   instr_list.Append(new assem::LabelInstr(temp::LabelFactory::LabelString(label_end), label_end));
    //   break;
    // case OR_OP:
    //   left = left_->Munch(instr_list, fs);
    //   right = right_->Munch(instr_list, fs);
    //   label_false = temp::LabelFactory::NewLabel();
    //   label_end = temp::LabelFactory::NewLabel();
    //   instr_list.Append(new assem::OperInstr("cmpq $0, `s0", nullptr, new temp::TempList(left), nullptr));
    //   instr_list.Append(new assem::OperInstr("jne " + temp::LabelFactory::LabelString(label_false), nullptr, nullptr, nullptr));
    //   instr_list.Append(new assem::OperInstr("cmpq $0, `s0", nullptr, new temp::TempList(right), nullptr));
    //   instr_list.Append(new assem::OperInstr("jne " + temp::LabelFactory::LabelString(label_false), nullptr, nullptr, nullptr));
    //   instr_list.Append(new assem::MoveInstr("movq $0, `d0", new temp::TempList(new_reg), nullptr));
    //   instr_list.Append(new assem::OperInstr("jmp " + temp::LabelFactory::LabelString(label_end), nullptr, nullptr, nullptr));
    //   instr_list.Append(new assem::LabelInstr(temp::LabelFactory::LabelString(label_false), label_false));
    //   instr_list.Append(new assem::MoveInstr("movq $1, `d0", new temp::TempList(new_reg), nullptr));
    //   instr_list.Append(new assem::LabelInstr(temp::LabelFactory::LabelString(label_end), label_end));
    //   break;
  }
  return new_reg;
}

temp::Temp *MemExp::Munch(assem::InstrList &instr_list, std::string_view fs) {
  temp::Temp *new_reg = temp::TempFactory::NewTemp();
  auto res = exp_->Munch(instr_list, fs);
  instr_list.Append(new assem::OperInstr("movq (`s0), `d0", new temp::TempList(new_reg), new temp::TempList(res), nullptr));
  return new_reg;
}

temp::Temp *TempExp::Munch(assem::InstrList &instr_list, std::string_view fs) {
  if (temp_ != reg_manager->FramePointer()) {
    return temp_;
  }
  temp::Temp* new_reg = temp::TempFactory::NewTemp();
  std::stringstream stream;
  stream << "leaq " << fs << "_framesize(`s0), `d0";
  std::string assem = stream.str();
  instr_list.Append(new assem::OperInstr(assem, new temp::TempList(new_reg), new temp::TempList(reg_manager->StackPointer()), nullptr));
  return new_reg;
}

temp::Temp *EseqExp::Munch(assem::InstrList &instr_list, std::string_view fs) {
  stm_->Munch(instr_list, fs);
  return exp_->Munch(instr_list, fs);
}

temp::Temp *NameExp::Munch(assem::InstrList &instr_list, std::string_view fs) {
  temp::Temp *new_reg = temp::TempFactory::NewTemp();
  std::stringstream stream;
  stream << "leaq " << temp::LabelFactory::LabelString(name_) << "(%rip), `d0";
  std::string assem = stream.str();
  instr_list.Append(new assem::OperInstr(assem, new temp::TempList(new_reg), nullptr, nullptr));
  return new_reg;
}

temp::Temp *ConstExp::Munch(assem::InstrList &instr_list, std::string_view fs) {
  temp::Temp *new_reg = temp::TempFactory::NewTemp();
  std::stringstream stream;
  stream << "movq $" << consti_ << ", `d0";
  std::string assem = stream.str();
  instr_list.Append(new assem::OperInstr(assem, new temp::TempList(new_reg), nullptr, nullptr));
  return new_reg;
}

temp::TempList *moveArgs(assem::InstrList &instr_list, temp::TempList *args) {
  auto res = new temp::TempList();
  int i = 1;
  for (auto &arg : args->GetList()) {
    if (i <= 6) {
      instr_list.Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(reg_manager->GetNthArg(i)), new temp::TempList(arg)));
      res->Append(reg_manager->GetNthArg(i));
    }
    else {
      instr_list.Append(new assem::OperInstr("subq $" + std::to_string(frame::wordsize) + ", %rsp", nullptr, nullptr, nullptr));
      instr_list.Append(new assem::OperInstr("movq `s0, (%rsp)", nullptr, new temp::TempList(arg), nullptr));
    }
    i++;
  }
  return res;
}

temp::Temp *CallExp::Munch(assem::InstrList &instr_list, std::string_view fs) {
  temp::Temp *new_reg = temp::TempFactory::NewTemp();

  tree::Exp *staticlink = args_->GetList().front();
  args_->PopStaticLink();

  auto res = staticlink->Munch(instr_list, fs);
  temp::Temp *oldSP = temp::TempFactory::NewTemp();
  instr_list.Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(oldSP), new temp::TempList(res)));

  std::string label = temp::LabelFactory::LabelString(((tree::NameExp*)fun_)->name_);
  auto args = args_->MunchArgs(instr_list, fs);
  auto to_be_protected = moveArgs(instr_list, args);

  instr_list.Append(new assem::OperInstr("subq $" + std::to_string(frame::wordsize) + ", %rsp", nullptr, nullptr, nullptr));
  instr_list.Append(new assem::OperInstr("movq `s0, (%rsp)", nullptr, new temp::TempList(oldSP), nullptr));
  instr_list.Append(new assem::OperInstr(std::string("callq ") + std::string(label), reg_manager->CallerSaves(), to_be_protected, nullptr));
  instr_list.Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(new_reg), new temp::TempList(reg_manager->RAX())));
  
  instr_list.Append(new assem::OperInstr("addq $" + std::to_string(frame::wordsize) + ", %rsp", nullptr, nullptr, nullptr));
  args_->ResetSP(instr_list, fs);
  return new_reg;
}

temp::TempList *ExpList::MunchArgs(assem::InstrList &instr_list, std::string_view fs) {
  auto res = new temp::TempList();
  for (auto &exp : exp_list_) {
    res->Append(exp->Munch(instr_list, fs));
  }
  return res;
}

void ExpList::ResetSP(assem::InstrList &instr_list, std::string_view fs) {
  int i = 1;
  for (auto &it : exp_list_) {
    if (i > 6) {
      std::stringstream stream;
      stream << "addq $" << frame::wordsize << ", %rsp";
      std::string assem = stream.str();
      instr_list.Append(new assem::OperInstr(assem, nullptr, nullptr, nullptr));
    }
    i++;
  }
}

void ExpList::PopStaticLink() {
  exp_list_.pop_front();
}

} // namespace tree
