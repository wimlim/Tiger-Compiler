#include "tiger/regalloc/regalloc.h"

#include "tiger/output/logger.h"

extern frame::RegManager *reg_manager;

namespace ra {

void RegAllocator::RegAlloc() {
  spilled_nodes_ = new live::INodeList();
  while (true) {
    fg::FlowGraphFactory flow_graph_factory(assem_instr_.get()->GetInstrList());
    flow_graph_factory.AssemFlowGraph();
    flow_graph_ = flow_graph_factory.GetFlowGraph();

    live::LiveGraphFactory live_graph_factory(flow_graph_);
    live_graph_factory.Liveness();
    live_graph_ = live_graph_factory.GetLiveGraph();

    col::Color color(live_graph_, not_spill_);
    color.Paint();
    auto col_result = color.GetResult();

    *spilled_nodes_ = *col_result.spills;
    
    if (spilled_nodes_->GetList().empty()) {
      result_ = std::make_unique<ra::Result>(col_result.coloring, assem_instr_.get()->GetInstrList());
      break;
    }
    else {
      delete result_->il_;
      delete result_->coloring_;
      RewriteProgram();
    }
  }
}

void RegAllocator::RewriteProgram() {
  for (auto& it : spilled_nodes_->GetList()) {
    auto instr_list = assem_instr_->GetInstrList();
    auto iter = instr_list->GetList().begin();

    while (iter != instr_list->GetList().end()) {
      auto instr = *iter;

      if (instr->Use()->Contain(it->NodeInfo()) || instr->Def()->Contain(it->NodeInfo())) {
        auto new_temp = temp::TempFactory::NewTemp();
        not_spill_.insert(new_temp);

        instr->Def()->Replace(it->NodeInfo(), new_temp);
        instr->Use()->Replace(it->NodeInfo(), new_temp);

        auto move_instr = new assem::OperInstr("movq `s0, (" + frame_->label_->Name() + "_framesize-" + std::to_string(-frame_->s_offset_) + ")(`d0)",
          new temp::TempList(reg_manager->StackPointer()), new temp::TempList(new_temp), nullptr);

        instr_list->Insert(iter, move_instr);
        ++iter;
      } else {
        ++iter;
      }
    }
  }
}


} // namespace ra