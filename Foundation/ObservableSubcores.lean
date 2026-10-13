import Foundation.ObservableRestriction

/-! Graph norm and subcore closure control for observable restrictions. -/
noncomputable section

namespace OperatorDerivativeRewrite.Foundation.ObservableSubcores
open ObservableRestriction

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (A : H →ₗ.[ℝ] E) (V : Submodule ℝ H)

/-- The graph norm is inherited exactly from the source graph; restriction
does not change the input or derivative norm. -/
theorem graph_norm_eq (f : (derivative A V).domain) :
    ‖((f : V), derivative A V f)‖ =
      ‖(((f : V) : H), A ⟨((f : V) : H),
        (derivative_domain A V (f : V)).mp f.property⟩)‖ := rfl

/-- Any partial operator contained in the maximal closed observable
restriction is closable. No density is required. -/
theorem subcore_closable
    (hA : A.IsClosed) (B : V →ₗ.[ℝ] E) (hB : B ≤ derivative A V) :
    B.IsClosable :=
  (derivative_isClosed A V hA).isClosable.leIsClosable hB

/-- The closure of any such subcore remains inside the maximal observable
restriction. Equality requires a separate graph-core theorem. -/
theorem subcore_closure_le
    (hA : A.IsClosed) (B : V →ₗ.[ℝ] E) (hB : B ≤ derivative A V) :
    B.closure ≤ derivative A V := by
  apply LinearPMap.le_of_le_graph
  rw [← (subcore_closable A V hA B hB).graph_closure_eq_closure_graph]
  calc
    B.graph.topologicalClosure ≤ (derivative A V).graph.topologicalClosure :=
      Submodule.topologicalClosure_mono (LinearPMap.le_graph_of_le hB)
    _ = (derivative A V).graph :=
      (derivative_isClosed A V hA).submodule_topologicalClosure_eq

end OperatorDerivativeRewrite.Foundation.ObservableSubcores

