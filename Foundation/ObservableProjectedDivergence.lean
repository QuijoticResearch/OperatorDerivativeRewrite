import Foundation.ObservableRestriction
import Foundation.OperatorDomains

/-! Projected source divergence as a one-sided inclusion in the adjoint
of a densely defined observable restriction. -/
noncomputable section
open Set

namespace OperatorDerivativeRewrite.Foundation.ObservableProjectedDivergence
open ObservableRestriction

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (A : H →ₗ.[ℝ] E) (V : Submodule ℝ H) [CompleteSpace V]

/-- Project the source divergence into the observable Hilbert subspace. -/
def projectedSourceDivergence (u : A.adjoint.domain) : V :=
  V.orthogonalProjectionOnto (A.adjoint u)

/-- The source adjoint identity restricts to the observable domain and
produces the projected source divergence pairing. -/
theorem projected_pairing
    (hA : Dense (A.domain : Set H))
    (u : A.adjoint.domain) (f : (derivative A V).domain) :
    inner ℝ (projectedSourceDivergence A V u) (f : V) =
      inner ℝ (u : E) (derivative A V f) := by
  have hp := V.inner_orthogonalProjectionOnto_eq_of_mem_right
    (f : V) (A.adjoint u)
  have hi := A.adjoint_isFormalAdjoint hA u
    ⟨(f : H), (derivative_domain A V f).mp f.property⟩
  change inner ℝ (A.adjoint u) (f : H) =
    inner ℝ (u : E) (A ⟨(f : H), _⟩) at hi
  change inner ℝ (V.orthogonalProjectionOnto (A.adjoint u)) (f : V) =
    inner ℝ (u : E) (A ⟨(f : H), _⟩)
  rw [hp]
  exact hi

/-- Every source-divergence integrand belongs to the observable adjoint
domain when the latter is densely defined. -/
theorem source_divergence_mem
    (hA : Dense (A.domain : Set H))
    (hD : Dense ((derivative A V).domain : Set V))
    (u : A.adjoint.domain) :
    (u : E) ∈ (derivative A V).adjoint.domain := by
  apply (mem_adjoint_domain_iff_representable (derivative A V) hD (u : E)).mpr
  exact ⟨projectedSourceDivergence A V u,
    projected_pairing A V hA u⟩

/-- The observable adjoint agrees with projected source divergence on
the embedded source-adjoint domain; no equality of full domains is claimed. -/
theorem divergence_source_value
    (hA : Dense (A.domain : Set H))
    (hD : Dense ((derivative A V).domain : Set V))
    (u : A.adjoint.domain) :
    (derivative A V).adjoint
      ⟨(u : E), source_divergence_mem A V hA hD u⟩ =
      projectedSourceDivergence A V u :=
  (derivative A V).adjoint_apply_eq hD
    ⟨(u : E), source_divergence_mem A V hA hD u⟩
    (projected_pairing A V hA u)

end OperatorDerivativeRewrite.Foundation.ObservableProjectedDivergence

