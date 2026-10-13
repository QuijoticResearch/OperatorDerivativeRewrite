import Foundation.ObservableProjectedDivergence

/-! The projected source divergence is a partial operator. Its closure remains
inside the full observable adjoint; equality needs a graph-core theorem. -/
noncomputable section
open Set

namespace OperatorDerivativeRewrite.Foundation.ObservableProjectedDivergenceClosure
open ObservableRestriction ObservableProjectedDivergence

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (A : H →ₗ.[ℝ] E) (V : Submodule ℝ H) [CompleteSpace V]

/-- Source-adjoint integrands with values projected into the observable space. -/
def projectedOperator : E →ₗ.[ℝ] V where
  domain := A.adjoint.domain
  toFun := {
    toFun := projectedSourceDivergence A V
    map_add' := fun u v => by
      change V.orthogonalProjectionOnto (A.adjoint (u + v)) =
        V.orthogonalProjectionOnto (A.adjoint u) +
          V.orthogonalProjectionOnto (A.adjoint v)
      rw [A.adjoint.map_add, map_add]
    map_smul' := fun c u => by
      change V.orthogonalProjectionOnto (A.adjoint (c • u)) =
        c • V.orthogonalProjectionOnto (A.adjoint u)
      rw [A.adjoint.map_smul, map_smul] }

/-- Every graph point of the projected source divergence is a graph point
of the full observable adjoint, under independent source and observable
density hypotheses. -/
theorem projectedOperator_le_adjoint
    (hA : Dense (A.domain : Set H))
    (hD : Dense ((derivative A V).domain : Set V)) :
    projectedOperator A V ≤ (derivative A V).adjoint := by
  apply LinearPMap.le_of_le_graph
  intro u hu
  obtain ⟨x, hx, heq⟩ := (projectedOperator A V).mem_graph_iff.mp hu
  have hm := source_divergence_mem A V hA hD x
  apply ((derivative A V).adjoint).mem_graph_iff.mpr
  refine ⟨⟨(x : E), hm⟩, ?_, ?_⟩
  · exact hx
  · change (derivative A V).adjoint ⟨(x : E), hm⟩ = _
    rw [divergence_source_value A V hA hD x]
    exact heq

/-- The initial projected divergence is closable. -/
theorem projectedOperator_closable
    (hA : Dense (A.domain : Set H))
    (hD : Dense ((derivative A V).domain : Set V)) :
    (projectedOperator A V).IsClosable :=
  ((derivative A V).adjoint_isClosed hD).isClosable.leIsClosable
    (projectedOperator_le_adjoint A V hA hD)

/-- Closing the projected source divergence cannot produce an integrand
outside the full observable adjoint graph. -/
theorem projectedOperator_closure_le_adjoint
    (hA : Dense (A.domain : Set H))
    (hD : Dense ((derivative A V).domain : Set V)) :
    (projectedOperator A V).closure ≤ (derivative A V).adjoint := by
  apply LinearPMap.le_of_le_graph
  rw [← (projectedOperator_closable A V hA hD).graph_closure_eq_closure_graph]
  calc
    (projectedOperator A V).graph.topologicalClosure ≤
        (derivative A V).adjoint.graph.topologicalClosure :=
      Submodule.topologicalClosure_mono
        (LinearPMap.le_graph_of_le (projectedOperator_le_adjoint A V hA hD))
    _ = (derivative A V).adjoint.graph :=
      ((derivative A V).adjoint_isClosed hD).submodule_topologicalClosure_eq

end OperatorDerivativeRewrite.Foundation.ObservableProjectedDivergenceClosure
