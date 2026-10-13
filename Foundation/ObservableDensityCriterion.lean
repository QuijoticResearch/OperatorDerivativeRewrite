import Foundation.ObservableCoreDensity

/-! Exact Hilbert-space criterion for density of an observable derivative
domain: absence of a nonzero observable vector orthogonal to every
differentiable observable. -/
noncomputable section

namespace OperatorDerivativeRewrite.Foundation.ObservableDensityCriterion
open ObservableRestriction

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (A : H →ₗ.[ℝ] E) (V : Submodule ℝ H) [CompleteSpace V]

/-- Observable-core density is equivalent to trivial orthogonal annihilator.
This condition is exact, unlike the sufficient projection-invariance criterion. -/
theorem derivative_dense_iff_annihilator_zero :
    Dense ((derivative A V).domain : Set V) ↔
      ∀ g : V, (∀ f : (derivative A V).domain,
        inner ℝ g (f : V) = 0) → g = 0 := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  simp only [Submodule.mem_orthogonal']
  constructor
  · intro h g hg
    exact h g (fun u hu => hg ⟨u, hu⟩)
  · intro h g hg
    exact h g (fun f => hg f.val f.property)

end OperatorDerivativeRewrite.Foundation.ObservableDensityCriterion

