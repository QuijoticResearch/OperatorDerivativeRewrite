import Foundation.Adjoint

/-! Closure and formal-adjoint arguments reusable beyond the one-dimensional Gaussian model. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation
open scoped Topology
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The graph closure of a closable operator is contained in every closed extension. -/
theorem operatorClosure_le_closed {T S : E →ₗ.[ℝ] F}
    (hT : T.IsClosable) (hS : S.IsClosed) (hTS : T ≤ S) : T.closure ≤ S := by
  apply LinearPMap.le_of_le_graph
  rw [← hT.graph_closure_eq_closure_graph]
  exact T.graph.topologicalClosure_minimal (LinearPMap.le_graph_of_le hTS) hS

/-- Density of the algebraic domain passes to the domain of its graph closure. -/
theorem operatorClosure_dense_domain {T : E →ₗ.[ℝ] F}
    (hT : Dense (T.domain : Set E)) : Dense (T.closure.domain : Set E) :=
  hT.mono T.le_closure.1

/-- A formal-adjoint identity extends to the graph closure on one side. -/
theorem formalAdjoint_closure_left {T : E →ₗ.[ℝ] F} {S : F →ₗ.[ℝ] E}
    (hT : T.IsClosable) (h : T.IsFormalAdjoint S) : T.closure.IsFormalAdjoint S := by
  intro x y
  have hx : ((x : E), T.closure x) ∈ T.graph.topologicalClosure := by
    rw [hT.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph x
  exact (closure_minimal (s := (T.graph : Set (E × F)))
    (t := {z | inner ℝ z.2 (y : F) = inner ℝ z.1 (S y)})
    (by
      rintro z hz
      obtain ⟨v, hv⟩ := (T.mem_graph_iff').mp hz
      rw [← hv]
      exact h v y)
    (isClosed_eq (continuous_snd.inner continuous_const)
      (continuous_fst.inner continuous_const))) hx

/-- Closing a densely defined closable operator does not change its adjoint. -/
theorem operatorClosure_adjoint_eq [CompleteSpace E] [CompleteSpace F]
    {T : E →ₗ.[ℝ] F} (hT : T.IsClosable) (hd : Dense (T.domain : Set E)) :
    T.closure.adjoint = T.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (operatorClosure_dense_domain hd),
    LinearPMap.adjoint_graph_eq_graph_adjoint hd,
    ← hT.graph_closure_eq_closure_graph]
  ext z
  rw [Submodule.mem_adjoint_iff, Submodule.mem_adjoint_iff]
  constructor
  · intro h a b hab
    exact h a b (T.graph.le_topologicalClosure hab)
  · intro h a b hab
    exact (closure_minimal (s := (T.graph : Set (E × F)))
      (t := {w | inner ℝ w.2 z.1 - inner ℝ w.1 z.2 = 0})
      (fun w hw => h w.1 w.2 hw)
      (isClosed_eq ((continuous_snd.inner continuous_const).sub
        (continuous_fst.inner continuous_const)) continuous_const)) hab

end OperatorDerivativeRewrite.Foundation
