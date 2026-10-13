import Foundation.ObservableProjectedDivergence

/-! A verifiable sufficient condition for density of an observable
restriction domain: source-domain invariance under orthogonal projection. -/
noncomputable section
open Set

namespace OperatorDerivativeRewrite.Foundation.ObservableCoreDensity
open ObservableRestriction

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If the observable orthogonal projection preserves the source domain,
source-domain density transfers to the observable restriction. This is an
additional, testable condition, not a consequence of source density. -/
theorem derivative_dense_of_projection_invariant
    (A : H →ₗ.[ℝ] E) (V : Submodule ℝ H) [CompleteSpace V]
    (hA : Dense (A.domain : Set H))
    (hstable : ∀ x ∈ A.domain, ((V.orthogonalProjectionOnto x : V) : H) ∈ A.domain) :
    Dense ((derivative A V).domain : Set V) := by
  have hsurj : Function.Surjective V.orthogonalProjectionOnto := by
    intro v
    exact ⟨(v : H), V.orthogonalProjectionOnto_mem_subspace_eq_self v⟩
  apply hsurj.denseRange.dense_of_mapsTo V.orthogonalProjectionOnto.continuous hA
  intro x hx
  exact (derivative_domain A V (V.orthogonalProjectionOnto x)).2 (hstable x hx)

end OperatorDerivativeRewrite.Foundation.ObservableCoreDensity

