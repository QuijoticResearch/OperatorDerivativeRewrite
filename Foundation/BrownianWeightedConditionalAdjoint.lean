import Foundation.BrownianWeightedRepresentation
import Foundation.GaussianFiniteHorizonAdjoint

/-! The whole-ambient weighted adjoint reconstructs centered conditional expectation. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianWeightedConditionalAdjoint
open InfiniteGaussian GaussianConditionalIto BrownianWeightedPredictableIntegral
open BrownianWeightedSquareAdjoint BrownianWeightedRepresentation
open GaussianTimeProductL2 GaussianPredictableFull GaussianPredictableAdjoint
open BrownianClockWeightedEnergy

local instance (T : ℝ≥0) : CompleteSpace (domain T) := (domain_isClosed T).completeSpace_coe

theorem adjoint_pastProjection (T : ℝ≥0) (F : GaussianL2) :
    adjoint T (pastProjection T F) = adjoint T F := by
  apply ext_inner_right ℝ
  intro u
  change inner ℝ ((integral T).toContinuousLinearMap.adjoint (pastProjection T F)) u =
    inner ℝ ((integral T).toContinuousLinearMap.adjoint F) u
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ ((pastL2 T).starProjection F) (integral T u) = _
  rw [Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (integral_mem_past T u)]
  rfl

theorem all_L2_representation (T : ℝ≥0) (F : GaussianL2) :
    integral T (adjoint T F) =
      pastProjection T F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  rw [← adjoint_pastProjection T F]
  rw [representation T (pastProjection T F) ((pastL2 T).starProjection_apply_mem F),
    GaussianFiniteHorizonAdjoint.pastProjection_integral_mean]

theorem adjoint_zero_iff (T : ℝ≥0) (F : GaussianL2) :
    adjoint T F = 0 ↔ pastProjection T F = (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  constructor
  · intro h
    have he := all_L2_representation T F
    rw [h, map_zero] at he
    exact sub_eq_zero.mp he.symm
  · intro h
    apply (integral T).injective
    rw [map_zero, all_L2_representation, h, sub_self]

theorem reconstruction_fixed_iff (T : ℝ≥0) (F : GaussianL2) :
    integral T (adjoint T F) = F ↔
      F ∈ pastL2 T ∧ (∫ ω, F ω ∂gaussianProduct) = 0 := by
  constructor
  · intro h
    apply (range_iff T F).mp
    exact ⟨adjoint T F, h⟩
  · intro h
    obtain ⟨u,hu⟩ := (range_iff T F).mpr h
    change integral T u = F at hu
    rw [← hu, adjoint_integral]

theorem adjoint_bound (T : ℝ≥0) : ‖adjoint T‖ ≤ 1 := by
  change ‖(integral T).toContinuousLinearMap.adjoint‖ ≤ 1
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact (integral T).norm_toContinuousLinearMap_le

theorem quotient_coeFn (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ pastL2 T) :
    (adjoint T F : Lp ℝ 2 (energy T)) =ᵐ[energy T]
      fun z => (predictableAdjoint F : TimeProbabilityL2) z / sigma z := by
  rw [adjoint_eq_pullback T F hF]
  exact pullback_coeFn T (predictableAdjoint F)

theorem clark_ocone_representer (T : ℝ≥0) (F : closedCylindricalDerivative.domain)
    (hF : (F : GaussianL2) ∈ pastL2 T) :
    adjoint T (F : GaussianL2) =
      pullback T (predictableProjection (closedCylindricalDerivative F)) := by
  rw [adjoint_eq_pullback T (F : GaussianL2) hF,
    predictableAdjoint_eq_projected_derivative]

end OperatorDerivativeRewrite.Foundation.BrownianWeightedConditionalAdjoint
