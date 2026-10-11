import Foundation.AdjointClosure
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! The bidual identity for closed densely defined real Hilbert operators.
Adjoint-domain density is explicit; no essential-adjointness or core condition is used. -/
noncomputable section
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A closed densely defined operator with densely defined adjoint equals its bidual.
The reverse inclusion is proved by orthogonal separation of the closed graph. -/
theorem closedOperator_adjoint_adjoint_eq {T : E →ₗ.[ℝ] F}
    (hT : T.IsClosed) (hd : Dense (T.domain : Set E))
    (ha : Dense (T.adjoint.domain : Set F)) : T.adjoint.adjoint = T := by
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    rintro ⟨x, y⟩ hz
    let K : Submodule ℝ (WithLp 2 (E × F)) :=
      T.graph.comap (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap
    have hK : IsClosed (K : Set (WithLp 2 (E × F))) :=
      hT.preimage (WithLp.prod_continuous_ofLp 2 E F)
    have hKK : K.orthogonal.orthogonal = K := by
      rw [K.orthogonal_orthogonal_eq_closure, hK.submodule_topologicalClosure_eq]
    have hx : WithLp.toLp 2 (x, y) ∈ K.orthogonal.orthogonal := by
      intro w hw
      have hwgraph : ((WithLp.ofLp w).2, -(WithLp.ofLp w).1) ∈ T.adjoint.graph := by
        rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd, Submodule.mem_adjoint_iff]
        intro a b hab
        have hh := hw (WithLp.toLp 2 (a, b)) hab
        simp only [WithLp.prod_inner_apply] at hh
        simp only [inner_neg_right, sub_neg_eq_add]
        linarith
      rw [LinearPMap.adjoint_graph_eq_graph_adjoint ha, Submodule.mem_adjoint_iff] at hz
      have hh := hz _ _ hwgraph
      simp only [inner_neg_left] at hh
      simp only [WithLp.prod_inner_apply]
      linarith
    rw [hKK] at hx
    exact hx
  · exact (T.adjoint_isFormalAdjoint hd).le_adjoint ha

/-- A densely defined closable operator with densely defined adjoint has its actual graph
closure as bidual. The density hypotheses concern ambient L², never the graph norm. -/
theorem closableOperator_adjoint_adjoint_eq_closure {T : E →ₗ.[ℝ] F}
    (hT : T.IsClosable) (hd : Dense (T.domain : Set E))
    (ha : Dense (T.adjoint.domain : Set F)) : T.adjoint.adjoint = T.closure := by
  have hca : Dense (T.closure.adjoint.domain : Set F) := by
    rw [operatorClosure_adjoint_eq hT hd]
    exact ha
  have h := closedOperator_adjoint_adjoint_eq hT.closure_isClosed
    (operatorClosure_dense_domain hd) hca
  rw [operatorClosure_adjoint_eq hT hd] at h
  exact h

end OperatorDerivativeRewrite.Foundation
