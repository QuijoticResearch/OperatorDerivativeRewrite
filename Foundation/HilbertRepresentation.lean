import Foundation.AdjointClosure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Hilbert representation without multiplication assumptions

The adjoint of a Hilbert-space isometry is defined on the whole target space.
It agrees with the predictable projection of an unbounded adjoint only on that
adjoint's actual domain. No process, filtration, or stochastic realization is
asserted by this abstract module.
-/

noncomputable section
open scoped Topology

namespace OperatorDerivativeRewrite.Foundation.HilbertRepresentation

variable {V X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- The actual everywhere-defined bounded adjoint of the given isometry. -/
def predictableAdjoint (J : V →ₗᵢ[ℝ] X) : X →L[ℝ] V :=
  J.toContinuousLinearMap.adjoint

/-- The actual adjoint pairing; no full unbounded derivative is used. -/
theorem predictableAdjoint_pairing (J : V →ₗᵢ[ℝ] X) (F : X) (u : V) :
    inner ℝ (predictableAdjoint J F) u = inner ℝ F (J u) :=
  J.toContinuousLinearMap.adjoint_inner_left u F

/-- The adjoint is a left inverse to the isometry. -/
theorem predictableAdjoint_isometry_apply (J : V →ₗᵢ[ℝ] X) (u : V) :
    predictableAdjoint J (J u) = u := by
  exact congrArg (fun A : V →L[ℝ] V => A u) J.adjoint_comp_self

/-- The represented component, constructed by applying J to its actual adjoint. -/
def representationProjection (J : V →ₗᵢ[ℝ] X) : X →L[ℝ] X :=
  J.toContinuousLinearMap.comp (predictableAdjoint J)

omit [CompleteSpace X] in
/-- Completeness and isometry prove closed range; it is not an extra assumption. -/
theorem isClosed_isometry_range (J : V →ₗᵢ[ℝ] X) :
    IsClosed (J.toLinearMap.range : Set X) := by
  exact J.isometry.isClosedEmbedding.isClosed_range

/-- The represented component belongs to the actual isometry range. -/
theorem representationProjection_mem_range (J : V →ₗᵢ[ℝ] X) (F : X) :
    representationProjection J F ∈ J.toLinearMap.range :=
  ⟨predictableAdjoint J F, rfl⟩

/-- GKW residual orthogonality follows from adjointness and isometry. -/
theorem representation_residual_pairing (J : V →ₗᵢ[ℝ] X) (F : X) (u : V) :
    inner ℝ (F - representationProjection J F) (J u) = 0 := by
  change inner ℝ (F - J (predictableAdjoint J F)) (J u) = 0
  rw [inner_sub_left, J.inner_map_map, predictableAdjoint_pairing, sub_self]

/-- The residual is orthogonal to the whole closed range, not merely a chosen test family. -/
theorem representation_residual_orthogonal (J : V →ₗᵢ[ℝ] X) (F : X) :
    F - representationProjection J F ∈ J.toLinearMap.rangeᗮ := by
  rw [Submodule.mem_orthogonal']
  rintro _ ⟨u, rfl⟩
  exact representation_residual_pairing J F u

/-- The represented component is exactly Mathlib's orthogonal projection onto any
identified closed range. Completeness of the range is already proved above. -/
theorem representationProjection_eq_starProjection
    (J : V →ₗᵢ[ℝ] X) (S : Submodule ℝ X) [CompleteSpace S]
    (hS : J.toLinearMap.range = S) (F : X) :
    representationProjection J F = S.starProjection F := by
  symm
  apply S.eq_starProjection_of_mem_orthogonal
  · rw [← hS]
    exact representationProjection_mem_range J F
  · rw [← hS]
    exact representation_residual_orthogonal J F

/-- Projection is idempotent on every input, with no PRP hypothesis. -/
theorem representationProjection_idempotent (J : V →ₗᵢ[ℝ] X) (F : X) :
    representationProjection J (representationProjection J F) =
      representationProjection J F := by
  change J (predictableAdjoint J (J (predictableAdjoint J F))) =
    J (predictableAdjoint J F)
  rw [predictableAdjoint_isometry_apply]

/-- Full representation holds precisely on the actual isometry range. -/
theorem representationProjection_eq_self_iff (J : V →ₗᵢ[ℝ] X) (F : X) :
    representationProjection J F = F ↔ F ∈ J.toLinearMap.range := by
  constructor
  · intro h
    rw [← h]
    exact representationProjection_mem_range J F
  · rintro ⟨u, rfl⟩
    change J (predictableAdjoint J (J u)) = J u
    rw [predictableAdjoint_isometry_apply]

/-- The variance/GKW norm decomposition is a genuine Hilbert Pythagorean identity. -/
theorem representation_norm_decomposition (J : V →ₗᵢ[ℝ] X) (F : X) :
    ‖F‖ ^ 2 = ‖predictableAdjoint J F‖ ^ 2 +
      ‖F - representationProjection J F‖ ^ 2 := by
  have hp := norm_add_sq_real (F - representationProjection J F)
    (representationProjection J F)
  have hz : inner ℝ (F - representationProjection J F)
      (representationProjection J F) = 0 :=
    representation_residual_pairing J F (predictableAdjoint J F)
  have hn : ‖representationProjection J F‖ = ‖predictableAdjoint J F‖ :=
    J.norm_map _
  rw [sub_add_cancel, hz, hn] at hp
  linarith

/-- When the range is the complement of a closed constants subspace, the represented
component is exactly centering. The range equality is the explicit abstract PRP input. -/
theorem representation_of_range_eq_orthogonal
    (J : V →ₗᵢ[ℝ] X) (C : Submodule ℝ X) [CompleteSpace C]
    (hRange : J.toLinearMap.range = Cᗮ) (F : X) :
    representationProjection J F = F - C.starProjection F := by
  rw [representationProjection_eq_starProjection J Cᗮ hRange]
  exact C.starProjection_orthogonal_val F

/-- Under the explicit range/PRP equality, the centered norm equals the integrand norm. -/
theorem representation_norm_identity
    (J : V →ₗᵢ[ℝ] X) (C : Submodule ℝ X) [CompleteSpace C]
    (hRange : J.toLinearMap.range = Cᗮ) (F : X) :
    ‖F - C.starProjection F‖ ^ 2 = ‖predictableAdjoint J F‖ ^ 2 := by
  rw [← representation_of_range_eq_orthogonal J C hRange F]
  exact congrArg (fun r : ℝ => r ^ 2) (J.norm_map (predictableAdjoint J F))

omit [CompleteSpace X] in
/-- The unbounded adjoint domain is exactly ambient-norm boundedness of its pairing.
The norm on a test vector is the original V norm, not the graph norm. -/
theorem adjoint_domain_iff_pairing_bound (T : V →ₗ.[ℝ] X)
    (hDense : Dense (T.domain : Set V)) (F : X) :
    F ∈ T.adjoint.domain ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : T.domain,
      |inner ℝ F (T u)| ≤ C * ‖(u : V)‖ := by
  constructor
  · intro hF
    refine ⟨‖T.adjoint ⟨F, hF⟩‖, norm_nonneg _, fun u => ?_⟩
    rw [← T.adjoint_isFormalAdjoint hDense ⟨F, hF⟩ u]
    exact abs_real_inner_le_norm _ _
  · rintro ⟨C, _, hC⟩
    rw [T.mem_adjoint_domain_iff]
    let l : T.domain →ₗ[ℝ] ℝ := (innerSL ℝ F).toLinearMap.comp T.toFun
    have hl : ∀ u : T.domain, ‖l u‖ ≤ C * ‖u‖ := by
      intro u
      change |inner ℝ F (T u)| ≤ C * ‖(u : V)‖
      exact hC u
    exact (l.mkContinuous C hl).continuous

omit [CompleteSpace X] in
/-- Density makes the represented vector unique; no stochastic structure is involved. -/
theorem adjoint_representer_unique (T : V →ₗ.[ℝ] X)
    (hDense : Dense (T.domain : Set V)) (F : X) (v w : V)
    (hv : ∀ u : T.domain, inner ℝ v (u : V) = inner ℝ F (T u))
    (hw : ∀ u : T.domain, inner ℝ w (u : V) = inner ℝ F (T u)) : v = w := by
  have hF : F ∈ T.adjoint.domain := T.mem_adjoint_domain_of_exists F ⟨v, hv⟩
  exact (T.adjoint_apply_eq hDense ⟨F, hF⟩ hv).symm.trans
    (T.adjoint_apply_eq hDense ⟨F, hF⟩ hw)

/-- An actual graph core suffices to check the ambient-norm adjoint bound.
The hypothesis is equality with the graph closure, not ambient domain density alone. -/
theorem adjoint_domain_iff_core_pairing_bound (S T : V →ₗ.[ℝ] X)
    (hS : S.IsClosable) (hDense : Dense (S.domain : Set V))
    (hCore : T = S.closure) (F : X) :
    F ∈ T.adjoint.domain ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : S.domain,
      |inner ℝ F (S u)| ≤ C * ‖(u : V)‖ := by
  rw [hCore, operatorClosure_adjoint_eq hS hDense]
  exact adjoint_domain_iff_pairing_bound S hDense F

section PredictableSubspace
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
variable (P : Submodule ℝ K) [CompleteSpace P]

/-- If the given partial divergence extends the isometry on P, then its full adjoint
agrees after projection with the bounded predictable adjoint on its actual domain. -/
theorem predictableAdjoint_eq_projected_adjoint (J : P →ₗᵢ[ℝ] X)
    (δ : K →ₗ.[ℝ] X) (hDense : Dense (δ.domain : Set K))
    (hdom : P ≤ δ.domain)
    (hExt : ∀ u : P, δ ⟨(u : K), hdom u.property⟩ = J u)
    (F : δ.adjoint.domain) :
    predictableAdjoint J (F : X) = P.orthogonalProjectionOnto (δ.adjoint F) := by
  apply ext_inner_right ℝ
  intro u
  rw [predictableAdjoint_pairing, P.inner_orthogonalProjectionOnto_eq_of_mem_right]
  have hp := δ.adjoint_isFormalAdjoint hDense F ⟨(u : K), hdom u.property⟩
  rw [hExt] at hp
  exact hp.symm

end PredictableSubspace
end OperatorDerivativeRewrite.Foundation.HilbertRepresentation
