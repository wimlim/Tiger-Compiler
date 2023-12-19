#include "tiger/liveness/flowgraph.h"

namespace fg {
  
void FlowGraphFactory::AssemFlowGraph() {
  auto label2node = label_map_.get();
  tab::Table<assem::Instr, FNode> instr2node;

  FNodePtr prev = nullptr;
  for (auto &instruction : instr_list_->GetList()) {
    auto current_node = flowgraph_->NewNode(instruction);
    instr2node.Enter(instruction, current_node);

    if (prev) {
      flowgraph_->AddEdge(prev, current_node);
    }

    if (instruction->kind_ == assem::Instr::LABEL) {
      label2node->Enter(static_cast<assem::LabelInstr*>(instruction)->label_, current_node);
    }

    if (instruction->kind_ == assem::Instr::OPER && ((assem::OperInstr*)instruction)->assem_.find("jmp") == 0) {
      prev = nullptr;
    }
    else {
      prev = current_node;
    }
  }

  for (auto &instruction : instr_list_->GetList()) {
    if (instruction->kind_ == assem::Instr::OPER && ((assem::OperInstr*)instruction)->jumps_) {
      for (auto &label : *((assem::OperInstr*)instruction)->jumps_->labels_) {
        auto jmp_node = instr2node.Look(instruction);
        auto label_node = label2node->Look(label);
        flowgraph_->AddEdge(jmp_node, label_node);
      }
    }
  }
}

} // namespace fg

namespace assem {

temp::TempList *LabelInstr::Def() const {
  return new temp::TempList();
}

temp::TempList *MoveInstr::Def() const {
  return dst_ ? dst_ : new temp::TempList();
}

temp::TempList *OperInstr::Def() const {
  return dst_ ? dst_ : new temp::TempList();
}

temp::TempList *LabelInstr::Use() const {
  return new temp::TempList();
}

temp::TempList *MoveInstr::Use() const {
  return src_ ? src_ : new temp::TempList();
}

temp::TempList *OperInstr::Use() const {
  return src_ ? src_ : new temp::TempList();
}
} // namespace assem
