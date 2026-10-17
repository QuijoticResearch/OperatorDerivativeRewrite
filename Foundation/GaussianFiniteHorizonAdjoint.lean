import Foundation.GaussianRoughFiniteHorizon

/-! The everywhere-defined finite-horizon adjoint, identified on actual L2 classes. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianFiniteHorizonAdjoint
open InfiniteGaussian GaussianTimeProductL2 GaussianPredictableFull
open GaussianPredictableAdjoint GaussianRoughFiniteHorizon GaussianPredictableHorizon
open GaussianConditionalIto GaussianPredictableCutoff PredictableRealL2
set_option backward.isDefEq.respectTransparency false
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe
local instance (T : ℝ≥0) : CompleteSpace (PredictableDomain T) :=
  (isClosed_aestronglyMeasurable
    (predictable_le GaussianTimeProcess.naturalFiltration)).completeSpace_coe

/-- Actual zero extension into the full predictable space. -/
def extendPredictable (T : ℝ≥0) : PredictableDomain T →ₗᵢ[ℝ] fullPredictable :=
  domainEquiv.symm.toLinearIsometry.comp (horizonEmbedding T)

theorem restriction_extension_duality (T : ℝ≥0) (U : fullPredictable)
    (V : PredictableDomain T) :
    inner ℝ (restrictPredictable T U) V = inner ℝ U (extendPredictable T V) := by
  change inner ℝ (LpToLpRestrictCLM _ ℝ ℝ timeProbability 2 (horizon T)
    (U : TimeProbabilityL2)) (V : Lp ℝ 2 (horizonMeasure T gaussianProduct)) =
      inner ℝ (U : TimeProbabilityL2) (L2ZeroExtension (horizon_measurable T) V.val)
  rw [L2_inner_eq_integral, L2_inner_eq_integral]
  calc
    _ = ∫ z, inner ℝ ((U : TimeProbabilityL2) z)
        ((V : Lp ℝ 2 (horizonMeasure T gaussianProduct)) z)
        ∂horizonMeasure T gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [LpToLpRestrictCLM_coeFn ℝ (horizon T) (U : TimeProbabilityL2)]
        with z hz
      rw [hz]
    _ = ∫ z, (horizon T).indicator (fun z => inner ℝ ((U : TimeProbabilityL2) z)
        ((V : Lp ℝ 2 (horizonMeasure T gaussianProduct)) z)) z ∂timeProbability :=
      (integral_indicator (horizon_measurable T)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [L2ZeroExtension_coeFn (horizon_measurable T) V.val] with z hz
      rw [hz]
      by_cases h : z ∈ horizon T <;> simp [h]

theorem finite_integral_eq_extended (T : ℝ≥0) (V : PredictableDomain T) :
    GaussianPredictableHorizon.itoIntegral T V =
      GaussianPredictableFull.itoIntegral (extendPredictable T V) := by
  change GaussianPredictableL2Completion.productIntegral _ =
    GaussianPredictableL2Completion.productIntegral _
  exact congrArg GaussianPredictableL2Completion.productIntegral
    (domainEquiv.apply_symm_apply (horizonEmbedding T V)).symm

/-- This is the adjoint of the bounded finite-horizon integral, not the full divergence. -/
def finiteAdjoint (T : ℝ≥0) : GaussianL2 →L[ℝ] PredictableDomain T :=
  (GaussianPredictableHorizon.itoIntegral T).toContinuousLinearMap.adjoint

theorem finiteAdjoint_eq_restriction (T : ℝ≥0) (F : GaussianL2) :
    finiteAdjoint T F = restrictPredictable T (predictableAdjoint F) := by
  apply ext_inner_right ℝ
  intro V
  rw [restriction_extension_duality]
  change inner ℝ ((GaussianPredictableHorizon.itoIntegral T).toContinuousLinearMap.adjoint F) V =
    inner ℝ (GaussianPredictableFull.itoIntegral.toContinuousLinearMap.adjoint F)
      (extendPredictable T V)
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  exact congrArg (inner ℝ F) (finite_integral_eq_extended T V)

theorem finiteAdjoint_on_full_derivative (T : ℝ≥0) (F : closedCylindricalDerivative.domain) :
    finiteAdjoint T F =
      restrictPredictable T (predictableProjection (closedCylindricalDerivative F)) := by
  rw [finiteAdjoint_eq_restriction, predictableAdjoint_eq_projected_derivative]

theorem finiteAdjoint_representation (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ pastL2 T) :
    GaussianPredictableHorizon.itoIntegral T (finiteAdjoint T F) =
      F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  rw [finiteAdjoint_eq_restriction, restricted_integral,
    GaussianConditionalClarkOcone.past_representer_supported T F hF]
  exact GaussianBrownianPRP.brownian_representation F
    (GaussianConditionalClarkOcone.past_mem_brownian T hF)

theorem finiteAdjoint_conditional_representation (T : ℝ≥0) (F : GaussianL2)
    (hF : F ∈ GaussianBrownianGeneratedSpace.brownianL2) :
    GaussianPredictableHorizon.itoIntegral T (finiteAdjoint T F) =
      pastProjection T F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  rw [finiteAdjoint_eq_restriction, restricted_integral]
  exact GaussianConditionalClarkOcone.past_representation T F hF

theorem cut_extended (T : ℝ≥0) (V : PredictableDomain T) :
    predictableCut T (extendPredictable T V) = extendPredictable T V := by
  apply Subtype.ext
  change cut T (L2ZeroExtension (horizon_measurable T) V.val) =
    L2ZeroExtension (horizon_measurable T) V.val
  apply Lp.ext
  filter_upwards [cut_coeFn T (L2ZeroExtension (horizon_measurable T) V.val),
    L2ZeroExtension_coeFn (horizon_measurable T) V.val] with z hc he
  rw [hc]
  by_cases h : z ∈ horizon T
  · simp [h]
  · simp [h, he]

theorem finite_integral_mem_past (T : ℝ≥0) (V : PredictableDomain T) :
    GaussianPredictableHorizon.itoIntegral T V ∈ pastL2 T := by
  rw [finite_integral_eq_extended]
  simpa only [cut_extended] using integral_cut_mem_past T (extendPredictable T V)

theorem finiteAdjoint_pastProjection (T : ℝ≥0) (F : GaussianL2) :
    finiteAdjoint T (pastProjection T F) = finiteAdjoint T F := by
  apply ext_inner_right ℝ
  intro V
  change inner ℝ ((GaussianPredictableHorizon.itoIntegral T).toContinuousLinearMap.adjoint
    (pastProjection T F)) V =
      inner ℝ ((GaussianPredictableHorizon.itoIntegral T).toContinuousLinearMap.adjoint F) V
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ ((pastL2 T).starProjection F) (GaussianPredictableHorizon.itoIntegral T V) = _
  rw [Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (finite_integral_mem_past T V)]
  rfl

theorem pastProjection_integral_mean (T : ℝ≥0) (F : GaussianL2) :
    (∫ ω, pastProjection T F ω ∂gaussianProduct) = (∫ ω, F ω ∂gaussianProduct) := by
  rw [← gaussianOne_inner_eq_integral, ← gaussianOne_inner_eq_integral]
  change inner ℝ gaussianOne ((pastL2 T).starProjection F) = _
  rw [← Submodule.inner_starProjection_left_eq_right]
  change inner ℝ (pastProjection T gaussianOne) F = _
  rw [GaussianConditionalClarkOcone.pastProjection_one]

/-- On the whole ambient L2 space, the represented component is centered
conditional expectation. -/
theorem finiteAdjoint_all_L2_representation (T : ℝ≥0) (F : GaussianL2) :
    GaussianPredictableHorizon.itoIntegral T (finiteAdjoint T F) =
      pastProjection T F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  rw [← finiteAdjoint_pastProjection T F]
  rw [finiteAdjoint_representation T (pastProjection T F)
    ((pastL2 T).starProjection_apply_mem F), pastProjection_integral_mean]

end OperatorDerivativeRewrite.Foundation.GaussianFiniteHorizonAdjoint
