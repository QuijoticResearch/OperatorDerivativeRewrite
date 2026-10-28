import Foundation.FourCubeChordIncidence
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! The explicit retained15 edges are an actual spanning tree of the16 cube
vertices. This certificate serves the Wilson-coordinate test. -/
namespace OperatorDerivativeRewrite.Foundation.FourCubeAxialTree
open OneSidedBlockIncidence FourCubeChordIncidence

def graph : SimpleGraph Vertex := SimpleGraph.fromRel (fun v w => v≠origin ∧ parent v=w)
instance graph_decidable : DecidableRel graph.Adj := by unfold graph; infer_instance

theorem parent_nonfix : ∀ v : Vertex,v≠origin → v≠parent v := by decide

theorem connected : graph.Connected := by
  have hr (v : Vertex) : graph.Reachable v (parent v) := by
    by_cases hv : v=origin
    · subst v
      have hp : parent origin=origin := by decide
      rw [hp]
    · apply SimpleGraph.Adj.reachable
      rw [graph,SimpleGraph.fromRel_adj]
      exact ⟨parent_nonfix v hv,Or.inl ⟨hv,rfl⟩⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable (G := graph)).mpr
  refine ⟨origin,?_⟩
  intro v
  have he := (hr v).trans ((hr (parent v)).trans
    ((hr (parent (parent v))).trans (hr (parent (parent (parent v))))))
  have hp : parent (parent (parent (parent v)))=origin := parent_four v
  rw [hp] at he
  exact he.symm

theorem graph_edge_count : graph.edgeFinset.card=15 := by decide

theorem isTree : graph.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨connected,?_⟩
  rw [Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card,graph_edge_count]
  norm_num [Nat.card_eq_fintype_card,Fintype.card_fun]

theorem graph_iff_edges (v w : Vertex) : graph.Adj v w ↔
    ∃ e∈axialTree, (e.1=v ∧ shifted e.1 e.2=w) ∨ (e.1=w ∧ shifted e.1 e.2=v) := by
  fin_cases v <;> fin_cases w <;> decide

end OperatorDerivativeRewrite.Foundation.FourCubeAxialTree
