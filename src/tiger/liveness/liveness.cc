#include "tiger/liveness/liveness.h"

extern frame::RegManager *reg_manager;

namespace live {

bool MoveList::Contain(INodePtr src, INodePtr dst) {
  return std::any_of(move_list_.cbegin(), move_list_.cend(),
                     [src, dst](std::pair<INodePtr, INodePtr> move) {
                       return move.first == src && move.second == dst;
                     });
}

void MoveList::Delete(INodePtr src, INodePtr dst) {
  assert(src && dst);
  auto move_it = move_list_.begin();
  for (; move_it != move_list_.end(); move_it++) {
    if (move_it->first == src && move_it->second == dst) {
      break;
    }
  }
  move_list_.erase(move_it);
}

MoveList *MoveList::Union(MoveList *list) {
  auto *res = new MoveList();
  for (auto move : move_list_) {
    res->move_list_.push_back(move);
  }
  for (auto move : list->GetList()) {
    if (!res->Contain(move.first, move.second))
      res->move_list_.push_back(move);
  }
  return res;
}

MoveList *MoveList::Intersect(MoveList *list) {
  auto *res = new MoveList();
  for (auto move : list->GetList()) {
    if (Contain(move.first, move.second))
      res->move_list_.push_back(move);
  }
  return res;
}

std::set<temp::Temp *> ToSet(const std::list<temp::Temp *>& origin) {
  std::set<temp::Temp *> res;
  for (auto &it : origin)
    res.insert(it);
  return res;
}

temp::TempList* ToTempList(const std::set<temp::Temp *>& origin) {
  temp::TempList* res = new temp::TempList();
  for (auto &it : origin) 
    res->Append(it);
  return res;
}

void LiveGraphFactory::LiveMap() {
  for (auto &node : flowgraph_->Nodes()->GetList()) {
    in_->Enter(node, new temp::TempList());
    out_->Enter(node, new temp::TempList());
  }

  bool fixed = false;

  while (!fixed) {
    fixed = true;
    for (auto &node: flowgraph_->Nodes()->GetList()) {
      auto cur = node->NodeInfo();
      auto in_1 = ToSet(out_->Look(node)->GetList());

      for (auto &iter : cur->Def()->GetList())
        in_1.erase(iter);
      for (auto &iter : cur->Use()->GetList())
        in_1.insert(iter);
      if (in_1 != ToSet(in_->Look(node)->GetList())) {
        fixed = false;
        in_->Set(node, ToTempList(in_1));
      }

      std::set<temp::Temp *> out_1;
      for (auto &iter : node->Succ()->GetList())
        for (auto &iterator : in_->Look(iter)->GetList())
          out_1.insert(iterator);
      if (out_1 != ToSet(out_->Look(node)->GetList())) {
        fixed = false;
        out_->Set(node, ToTempList(out_1));
      }
    }
  }
}

void LiveGraphFactory::InterfGraph() {
  std::set<temp::Temp *> templist;
  
  for (auto &node : flowgraph_->Nodes()->GetList()) {
    for (auto &temp : node->NodeInfo()->Def()->GetList())
      templist.insert(temp);
    for (auto &temp : node->NodeInfo()->Use()->GetList())
      templist.insert(temp);
  }
  
  for (auto &reg : reg_manager->Registers()->GetList())
    templist.insert(reg);

  for (auto &temp : templist)
    temp_node_map_->Enter(temp, live_graph_.interf_graph->NewNode(temp));
  
  auto out = out_.get();

  for (auto &node : flowgraph_->Nodes()->GetList()) {
    auto &defs = node->NodeInfo()->Def()->GetList();
    auto &outs = out->Look(node)->GetList();
    for (auto &def : defs) {
      for (auto &outTemp : outs) {
        if (def != outTemp && !(node->NodeInfo()->kind_ == assem::Instr::MOVE && node->NodeInfo()->Use()->GetList().front() == outTemp)) {
          auto defNode = temp_node_map_->Look(def);
          auto outNode = temp_node_map_->Look(outTemp);
          live_graph_.interf_graph->AddEdge(defNode, outNode);
          live_graph_.interf_graph->AddEdge(outNode, defNode);
        }
      }
    }
  }

  for (auto &node : flowgraph_->Nodes()->GetList()) {
    auto &defs = node->NodeInfo()->Def()->GetList();
    auto &uses = node->NodeInfo()->Use()->GetList();
    auto &outs = out->Look(node)->GetList();
    if (node->NodeInfo()->kind_ == assem::Instr::MOVE && !defs.empty() && !uses.empty()) {
      for (auto &def : defs) {
        for (auto &outTemp : outs) {
          if (!std::count(uses.begin(), uses.end(), outTemp)) {
            auto defNode = temp_node_map_->Look(def);
            auto outNode = temp_node_map_->Look(outTemp);
            live_graph_.interf_graph->AddEdge(defNode, outNode);
            live_graph_.interf_graph->AddEdge(outNode, defNode);
          }
        }
        for (auto &use : uses) {
          live_graph_.moves->Fusion(temp_node_map_->Look(use), temp_node_map_->Look(def));
        }
      }
    }
  }

  auto &registers = reg_manager->Registers()->GetList();
  for (auto &reg1 : registers) {
    for (auto &reg2 : registers) {
      if (reg1 != reg2) {
        auto reg1Node = temp_node_map_->Look(reg1);
        auto reg2Node = temp_node_map_->Look(reg2);
        live_graph_.interf_graph->AddEdge(reg1Node, reg2Node);
        live_graph_.interf_graph->AddEdge(reg2Node, reg1Node);
      }
    }
  }
}

void LiveGraphFactory::Liveness() {
  LiveMap();
  InterfGraph();
}

} // namespace live
