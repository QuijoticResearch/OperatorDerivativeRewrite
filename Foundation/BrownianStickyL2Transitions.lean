import Foundation.BrownianTimeChangedConditionalKernel
import Foundation.L2GeneratedSubspace
import Foundation.HilbertRepresentation

/-! Actual two-time L2 contractions of the constructed sticky candidate.
The Hilbert adjoints and conditional kernels are identified. Composition is
expressed by an exact memory residual, rather than assumed as a semigroup law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianStickyL2Transitions
open InfiniteGaussian BrownianTimeChangedConditionalKernel HilbertRepresentation
set_option backward.isDefEq.respectTransparency false

abbrev StateL2 (κ t : ℝ≥0) := Lp ℝ 2 (marginal κ t)

def state_preserving (κ t : ℝ≥0) : MeasurePreserving (state κ t) gaussianProduct (marginal κ t) :=
  ⟨state_measurable κ t,rfl⟩

def embedding (κ t : ℝ≥0) : StateL2 κ t →ₗᵢ[ℝ] GaussianL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (state κ t) (state_preserving κ t)

theorem embedding_coeFn (κ t : ℝ≥0) (f : StateL2 κ t) :
    embedding κ t f =ᵐ[gaussianProduct] fun ω => f (state κ t ω) :=
  Lp.coeFn_compMeasurePreserving f (state_preserving κ t)

theorem embedding_range (κ t : ℝ≥0) : (embedding κ t).toLinearMap.range =
    lpMeas ℝ ℝ (MeasurableSpace.comap (state κ t) inferInstance) 2 gaussianProduct :=
  L2_pullback_range (state_preserving κ t)

def transition (κ s t : ℝ≥0) : StateL2 κ t →L[ℝ] StateL2 κ s :=
  (predictableAdjoint (embedding κ s)).comp (embedding κ t).toContinuousLinearMap

theorem transition_diagonal (κ t : ℝ≥0) (f : StateL2 κ t) : transition κ t t f = f :=
  predictableAdjoint_isometry_apply (embedding κ t) f

theorem transition_pairing (κ s t : ℝ≥0) (f : StateL2 κ t) (g : StateL2 κ s) :
    inner ℝ (transition κ s t f) g = inner ℝ (embedding κ t f) (embedding κ s g) :=
  predictableAdjoint_pairing (embedding κ s) (embedding κ t f) g

theorem transition_contraction (κ s t : ℝ≥0) (f : StateL2 κ t) :
    ‖transition κ s t f‖ ≤ ‖f‖ := by
  have h := representation_norm_decomposition (embedding κ s) (embedding κ t f)
  rw [(embedding κ t).norm_map] at h
  change ‖f‖^2 = ‖transition κ s t f‖^2+_ at h
  nlinarith [sq_nonneg (‖embedding κ t f-representationProjection (embedding κ s) (embedding κ t f)‖),
    norm_nonneg (transition κ s t f), norm_nonneg f]

theorem transition_adjoint (κ s t : ℝ≥0) : (transition κ s t).adjoint = transition κ t s := by
  unfold transition predictableAdjoint
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem current_projection_condExp (κ s : ℝ≥0) (F : GaussianL2) :
    representationProjection (embedding κ s) F =ᵐ[gaussianProduct]
      gaussianProduct[F | MeasurableSpace.comap (state κ s) inferInstance] := by
  letI : Fact (MeasurableSpace.comap (state κ s) inferInstance ≤
      (inferInstance : MeasurableSpace SampleSpace)) := ⟨(state_measurable κ s).comap_le⟩
  rw [representationProjection_eq_starProjection (embedding κ s)
    (lpMeas ℝ ℝ (MeasurableSpace.comap (state κ s) inferInstance) 2 gaussianProduct)
    (embedding_range κ s)]
  have h := (Lp.memLp F).condExpL2_ae_eq_condExp (𝕜 := ℝ) (state_measurable κ s).comap_le
  change (condExpL2 ℝ ℝ (state_measurable κ s).comap_le F : GaussianL2) =ᵐ[gaussianProduct]
    gaussianProduct[F | MeasurableSpace.comap (state κ s) inferInstance]
  simpa only [Lp.toLp_coeFn] using h

theorem transition_condExp (κ s t : ℝ≥0) (f : StateL2 κ t) :
    embedding κ s (transition κ s t f) =ᵐ[gaussianProduct]
      gaussianProduct[(fun ω => f (state κ t ω)) |
        MeasurableSpace.comap (state κ s) inferInstance] :=
  (current_projection_condExp κ s (embedding κ t f)).trans
    (condExp_congr_ae (embedding_coeFn κ t f))

theorem transition_kernel (κ s t : ℝ≥0) (f : StateL2 κ t) :
    embedding κ s (transition κ s t f) =ᵐ[gaussianProduct]
      (fun ω => ∫ y, f y ∂pairKernel κ s t (state κ s ω)) := by
  have hi : Integrable (fun ω => f (state κ t ω)) gaussianProduct :=
    ((Lp.memLp (embedding κ t f)).integrable (by norm_num)).congr (embedding_coeFn κ t f)
  exact (transition_condExp κ s t f).trans
    (condExp_ae_eq_integral_condDistrib (state_measurable κ s) (state_measurable κ t).aemeasurable
      (Lp.stronglyMeasurable f) hi)

theorem composition_defect (κ s t u : ℝ≥0) (f : StateL2 κ u) :
    transition κ s u f-transition κ s t (transition κ t u f) =
      predictableAdjoint (embedding κ s)
        (embedding κ u f-representationProjection (embedding κ t) (embedding κ u f)) := by
  unfold transition representationProjection
  simp only [ContinuousLinearMap.comp_apply, map_sub]
  rfl

theorem composition_iff_residual_zero (κ s t u : ℝ≥0) (f : StateL2 κ u) :
    transition κ s u f = transition κ s t (transition κ t u f) ↔
      predictableAdjoint (embedding κ s)
        (embedding κ u f-representationProjection (embedding κ t) (embedding κ u f)) = 0 := by
  rw [← composition_defect, sub_eq_zero]

end OperatorDerivativeRewrite.Foundation.BrownianStickyL2Transitions
