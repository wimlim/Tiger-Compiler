#ifndef TIGER_COMPILER_COLOR_H
#define TIGER_COMPILER_COLOR_H

#include "tiger/codegen/assem.h"
#include "tiger/frame/temp.h"
#include "tiger/liveness/liveness.h"
#include "tiger/util/graph.h"
#include <set>
#include <map>

namespace col {
struct Result {
  Result() : coloring(nullptr), spills(nullptr) {}
  Result(temp::Map *coloring, live::INodeListPtr spills)
      : coloring(coloring), spills(spills) {}
  temp::Map *coloring;
  live::INodeListPtr spills;
};

class Color {
public:
  explicit Color(live::LiveGraph live_graph, std::set<temp::Temp*> not_spill)
      : live_graph_(live_graph), not_spill_(not_spill) {}
  ~Color() {
    delete coalesced_moves_;
    delete constrained_moves_;
    delete frozen_moves_;
    delete worklist_moves_;
    delete active_moves_;
  }
  Result GetResult() {
    return result_;
  }

  void Paint();
  void Init();
  void Build();
  void Freeze();
  
  void MakeWorkList();
  void Simplify();
  void Coalesce();
  live::INodeListPtr Adjacent(live::INodePtr node);
  live::MoveList* NodeMoves(live::INodePtr node);
  bool MoveRelated(live::INodePtr node);
  void AddEdge(live::INodePtr, live::INodePtr);
  void DecrementDegree(live::INodePtr node);
  void EnableMoves(live::INodeListPtr nodelist);
  void AddWorkList(live::INodePtr u);
  bool OK(live::INodePtr t, live::INodePtr r);
  bool Conservertive(live::INodeListPtr nodes);
  live::INodePtr GetAlias(live::INodePtr n);
  void Combine(live::INodePtr u, live::INodePtr v);
  
  void FreezeMoves(live::INodePtr u);
  void SelectSpill();
  void AssignColor();

private:
  Result result_;
  live::LiveGraph live_graph_;
  fg::FGraphPtr flow_graph_;

  live::INodeListPtr precolored_;
  live::INodeListPtr initial_;

  live::INodeListPtr simplify_work_list_;
  live::INodeListPtr freeze_work_list_;
  live::INodeListPtr spill_work_list_;
  live::INodeListPtr spilled_nodes_;
  live::INodeListPtr coalesced_nodes_;
  live::INodeListPtr colored_nodes_;
  live::INodeListPtr select_stack_;

  live::MoveList* coalesced_moves_;
  live::MoveList* constrained_moves_;
  live::MoveList* frozen_moves_;
  live::MoveList* worklist_moves_;
  live::MoveList* active_moves_;

  std::set<std::pair<live::INodePtr, live::INodePtr>> adj_set_;
  std::map<live::INodePtr, live::INodeListPtr> adj_list_;
  std::map<live::INodePtr, int> degree_;
  std::map<live::INodePtr, live::MoveList*> move_list_;
  std::map<live::INodePtr, live::INodePtr> alias_;
  std::map<temp::Temp*, std::string> color_;
  std::set<temp::Temp*> not_spill_;

  int K;

private:
  bool Contain(live::INodePtr node, live::INodeListPtr list);
  live::INodeListPtr Union(live::INodeListPtr left, live::INodeListPtr right);
  live::INodeListPtr Sub(live::INodeListPtr left, live::INodeListPtr right);
  live::INodeListPtr Intersect(live::INodeListPtr left, live::INodeListPtr right);
  bool Contain(std::pair<live::INodePtr, live::INodePtr> node, live::MoveList* list);
  live::MoveList* Union(live::MoveList* left, live::MoveList* right);
  live::MoveList* Intersect(live::MoveList* left, live::MoveList* right);
};
} // namespace col

#endif // TIGER_COMPILER_COLOR_H
