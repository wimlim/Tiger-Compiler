#include "tiger/regalloc/color.h"

extern frame::RegManager *reg_manager;

namespace col {

void Color::Paint() {
  Init();
  for (auto node : live_graph_.interf_graph->Nodes()->GetList()) {
    adj_list_[node] = new live::INodeList();
    degree_[node] = 0;
  }
  Build();
  MakeWorkList();
  do {
    if (!simplify_work_list_->GetList().empty())
      Simplify();
    if (!worklist_moves_->GetList().empty())
      Coalesce();
    if (!freeze_work_list_->GetList().empty())
      Freeze();
    if (!spill_work_list_->GetList().empty())
      SelectSpill();
  } while (!simplify_work_list_->GetList().empty() || !worklist_moves_->GetList().empty()
    || !freeze_work_list_->GetList().empty() || !spill_work_list_->GetList().empty());
  AssignColor();
  result_.coloring = temp::Map::Empty();
  for (auto tmp : color_) {
    result_.coloring->Enter(tmp.first, new std::string(tmp.second));
  }
  result_.spills = new live::INodeList();
  for (auto node : spilled_nodes_->GetList()) {
    result_.spills->Fusion(node);
  }
}

void Color::Init() {
  K = reg_manager->Registers()->GetList().size();
  precolored_ = new live::INodeList();
  initial_ = new live::INodeList();
  simplify_work_list_ = new live::INodeList();
  freeze_work_list_ = new live::INodeList();
  spill_work_list_ = new live::INodeList();
  spilled_nodes_ = new live::INodeList();
  coalesced_nodes_ = new live::INodeList();
  colored_nodes_ = new live::INodeList();
  select_stack_ = new live::INodeList();
  coalesced_moves_ = new live::MoveList();
  constrained_moves_ = new live::MoveList();
  frozen_moves_ = new live::MoveList();
  worklist_moves_ = new live::MoveList();
  active_moves_ = new live::MoveList();
}

void Color::Build() {
  for (auto ele : live_graph_.moves->GetList()) {
    live::INodePtr src = ele.first;
    live::INodePtr dst = ele.second;
    if (move_list_.find(src) == move_list_.end()) move_list_[src] = new live::MoveList();
      move_list_[src]->Append(src, dst);
    if (move_list_.find(dst) == move_list_.end()) move_list_[dst] = new live::MoveList();
      move_list_[dst]->Append(src, dst);
  }
  worklist_moves_ = live_graph_.moves;
  for (auto node : live_graph_.interf_graph->Nodes()->GetList()) {
    for (auto adj : node->Adj()->GetList()) {
      AddEdge(node, adj);
      degree_[node] = 0;
    }
  }
  precolored_->Clear();
  std::list<temp::Temp *> regs = reg_manager->Registers()->GetList();
  for (auto node : live_graph_.interf_graph->Nodes()->GetList()) {
    std::string* name = reg_manager->temp_map_->Look(node->NodeInfo());
    if (name != NULL)
      precolored_->Fusion(node);
  }
  for (auto node : live_graph_.interf_graph->Nodes()->GetList()) {
    std::string* name = reg_manager->temp_map_->Look(node->NodeInfo());
    if (name != NULL)
      color_[node->NodeInfo()] = *name;
    else
      initial_->Fusion(node);
  }
}

void Color::MakeWorkList() {
  for (auto node : initial_->GetList()) {
    if (degree_[node] >= K)
      spill_work_list_->Fusion(node);
    else if (MoveRelated(node))
      freeze_work_list_->Fusion(node);
    else
      simplify_work_list_->Fusion(node);
  }
  initial_->Clear();
}

void Color::Simplify() {
  if (!(simplify_work_list_->GetList().empty())) {
    auto node = simplify_work_list_->GetList().front();
    simplify_work_list_->DeleteNode(node);
    select_stack_->Append(node);
    for (auto tmp : Adjacent(node)->GetList()) 
      DecrementDegree(tmp);
  }
}

void Color::Coalesce() {
  if (worklist_moves_->GetList().empty())
    return;
  auto m = worklist_moves_->GetList().front();
  live::INodePtr x = m.first;
  live::INodePtr y = m.second;
  x = GetAlias(x);
  y = GetAlias(y);
  live::INodePtr u = NULL;
  live::INodePtr v = NULL;
  if (precolored_->Contain(y)) {
    u = y;
    v = x;
  }
  else {
    u = x;
    v = y;
  }
  worklist_moves_->Delete(m.first, m.second);
  if (u == v) {
    coalesced_moves_->Fusion(m.first, m.second);
    AddWorkList(u);
  }
  else if (precolored_->Contain(v) || adj_set_.find(std::make_pair(u, v)) != adj_set_.end()) {
    constrained_moves_->Fusion(m.first, m.second);
    AddWorkList(u);
    AddWorkList(v);
  }
  else {
    bool flag = true;
    for (auto t : Adjacent(v)->GetList()) {
      if (!OK(t, u)) {
        flag = false;
        break;
      }
    }

    if (precolored_->Contain(u) && flag
      || !precolored_->Contain(u) && Conservertive(Union(Adjacent(u), Adjacent(v)))) {
        coalesced_moves_->Fusion(m.first, m.second);
        Combine(u, v);
        AddWorkList(u);
    }
    else
      active_moves_->Fusion(m.first, m.second);
  }
}

void Color::Freeze() {
  if (freeze_work_list_->GetList().empty()) {
    return;
  }
  auto u = freeze_work_list_->GetList().front();
  freeze_work_list_->DeleteNode(u);
  simplify_work_list_->Fusion(u);
  FreezeMoves(u);
}

void Color::SelectSpill() {
  live::INodePtr m = NULL;

  for (auto tmp : spill_work_list_->GetList()) {
    if (not_spill_.find(tmp->NodeInfo()) != not_spill_.end())
      continue;
    if (!spilled_nodes_->Contain(tmp) && !precolored_->Contain(tmp)) {
      m = tmp;
    }
  }

  if (!m) m = spill_work_list_->GetList().front();
  spill_work_list_->DeleteNode(m);
  simplify_work_list_->Fusion(m);
  FreezeMoves(m);
}

void Color::AssignColor() {
  auto nodes = select_stack_->GetList();
  while (!nodes.empty()) {
    auto currentNode = nodes.back();
    nodes.pop_back();

    std::vector<std::string> availableColors = reg_manager->Colors();

    for (auto adjNode : adj_list_[currentNode]->GetList()) {
      auto adjNodeAlias = GetAlias(adjNode);
      if (Union(colored_nodes_, precolored_)->Contain(adjNodeAlias)) {
        auto adjNodeColor = color_[adjNodeAlias->NodeInfo()];
        availableColors.erase(
          std::remove(availableColors.begin(), availableColors.end(), adjNodeColor),
          availableColors.end()
        );
      }
    }

    if (availableColors.empty()) {
      spilled_nodes_->Fusion(currentNode);
    }
    else {
      colored_nodes_->Fusion(currentNode);
      color_[currentNode->NodeInfo()] = availableColors.front();
    }
  }

  select_stack_->Clear();

  for (auto coalescedNode : coalesced_nodes_->GetList()) {
    auto aliasNode = GetAlias(coalescedNode);
    color_[coalescedNode->NodeInfo()] = color_[aliasNode->NodeInfo()];
  }
}


bool Color::Contain(live::INodePtr node, live::INodeListPtr list) {
  for (auto ele : list->GetList()) {
    if (ele->NodeInfo() == node->NodeInfo()) {
      return true;
    }
  }
  return false;
}

live::INodeListPtr Color::Union(live::INodeListPtr left, live::INodeListPtr right) {
  live::INodeListPtr result = new live::INodeList();
  for (auto ele : left->GetList())
    result->Fusion(ele);
  for (auto ele : right->GetList())
    result->Fusion(ele);
  return result;
}

live::INodeListPtr Color::Sub(live::INodeListPtr left, live::INodeListPtr right) {
  live::INodeListPtr result = new live::INodeList();
  for (auto ele : left->GetList()) {
    if (!Contain(ele, right)) {
      result->Append(ele);
    }
  }
  return result;
}

live::INodeListPtr Color::Intersect(live::INodeListPtr left, live::INodeListPtr right) {
  live::INodeListPtr result = new live::INodeList();
  for (auto ele : left->GetList()) {
    if (Contain(ele, right)) {
      result->Append(ele);
    }
  }
  return result;
}

bool Color::Contain(std::pair<live::INodePtr, live::INodePtr> node, live::MoveList* list) {
  bool ret = false;
  for (auto ele : list->GetList()) {
    if (ele == node) {
      ret = true;
      break;
    }
  }
  return false;
}

live::MoveList* Color::Union(live::MoveList* left, live::MoveList* right) {
  live::MoveList* result = new live::MoveList();
  for (auto ele : left->GetList())
    result->Fusion(ele.first, ele.second);
  for (auto ele : right->GetList()) 
    result->Fusion(ele.first, ele.second);
  return result;
}

live::MoveList* Color::Intersect(live::MoveList* left, live::MoveList* right) {
  live::MoveList* result = new live::MoveList();
  for (auto ele : left->GetList()) {
    if (Contain(ele, right)) {
      result->Append(ele.first, ele.second);
    }
  }
  return result;
}

void Color::AddEdge(live::INodePtr u, live::INodePtr v) {
  if (adj_set_.find(std::make_pair(u, v)) == adj_set_.end() && u != v) {
    adj_set_.insert(std::make_pair(u, v));
    adj_set_.insert(std::make_pair(v, u));
    if (!precolored_->Contain(u)) {
      adj_list_[u]->Fusion(v);
      degree_[u]++;
    }
    if (!precolored_->Contain(v)) {
      adj_list_[v]->Fusion(u);
      degree_[v]++;
    }
  }
}

live::INodeListPtr Color::Adjacent(live::INodePtr node) {
  if (adj_list_.find(node) == adj_list_.end()) {
    adj_list_[node] = new live::INodeList();
    return new live::INodeList();
  }
  return adj_list_[node]->Diff(Union(select_stack_, coalesced_nodes_));
}

live::MoveList* Color::NodeMoves(live::INodePtr node) {
  if (move_list_.find(node) == move_list_.end()) {
    move_list_[node] = new live::MoveList();
    return new live::MoveList();
  }
  return Intersect(move_list_[node], Union(active_moves_, worklist_moves_));
}

bool Color::MoveRelated(live::INodePtr node) {
  bool ret = !(NodeMoves(node)->GetList().empty());
  return ret;
}

void Color::DecrementDegree(live::INodePtr m) {
  int d = degree_[m];
  degree_[m] = d - 1;
  if (d == K) {
    live::INodeListPtr list = Adjacent(m);
    list->Fusion(m);
    EnableMoves(list);
    spill_work_list_->DeleteNode(m);
    if (MoveRelated(m)) freeze_work_list_->Fusion(m);
    else simplify_work_list_->Fusion(m);
  }
}

void Color::EnableMoves(live::INodeListPtr nodes) {
  for (auto n : nodes->GetList()) {
    for (auto m : NodeMoves(n)->GetList()) {
      if (active_moves_->Contain(m.first, m.second)) {
        active_moves_->Delete(m.first, m.second);
        worklist_moves_->Fusion(m.first, m.second);
      }
    }
  }
}

void Color::AddWorkList(live::INodePtr u) {
  if (!precolored_->Contain(u) && !MoveRelated(u) && degree_[u] < K) {
    freeze_work_list_->DeleteNode(u);
    simplify_work_list_->Fusion(u);
  }
}

bool Color::OK(live::INodePtr t, live::INodePtr r) {
  bool ret = degree_[t] < K || precolored_->Contain(t) || adj_set_.find(std::make_pair(t, r)) != adj_set_.end();
  return ret;
}

bool Color::Conservertive(live::INodeListPtr nodes) {
  int k = 0;
  for (auto n : nodes->GetList()) {
    if (degree_[n] >= K) {
      k++;
    }
  }
  return k < K;
}

live::INodePtr Color::GetAlias(live::INodePtr n) {
  if (coalesced_nodes_->Contain(n))
    return GetAlias(alias_[n]);
  else
    return n;
}

void Color::Combine(live::INodePtr u, live::INodePtr v) {
  if (freeze_work_list_->Contain(v)) {
    freeze_work_list_->DeleteNode(v);
  }
  else {
    spill_work_list_->DeleteNode(v);
  }

  coalesced_nodes_->Fusion(v);
  alias_[v] = u;
  move_list_[u] = Union(move_list_[u], move_list_[v]);
  
  live::INodeListPtr v_list = new live::INodeList();
  v_list->Append(v);
  EnableMoves(v_list);

  for (auto t : Adjacent(v)->GetList()) {
    AddEdge(t, u);
    DecrementDegree(t);
  }
  if (degree_[u] >= K && freeze_work_list_->Contain(u)) {
    freeze_work_list_->DeleteNode(u);
    spill_work_list_->Fusion(u);
  }
}

void Color::FreezeMoves(live::INodePtr u) {
  for (auto m : NodeMoves(u)->GetList()) {
    live::INodePtr x = m.first;
    live::INodePtr y = m.second;
    live::INodePtr v = NULL;
    if (GetAlias(y) == GetAlias(u)) {
      v = GetAlias(x);
    }
    else {
      v = GetAlias(y);
    }
    active_moves_->Delete(m.first, m.second);
    frozen_moves_->Fusion(m.first, m.second);
    if (NodeMoves(v)->GetList().empty() && degree_[v] < K) {
      freeze_work_list_->DeleteNode(v);
      simplify_work_list_->Fusion(v);
    }
  }
}

} // namespace col
