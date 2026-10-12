import Foundation.GaussianPredictableAdjoint

/-! The positive-time Brownian integral does not represent every centered random
variable in the larger ambient Gaussian product space. A concrete negative-time
first-chaos direction supplies the obstruction. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianAmbientRepresentationObstruction
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianContinuousRigidity
open GaussianPredictableFull GaussianPredictableAdjoint SeparableHilbertEmbedding
open GaussianTimePolynomialPairing
attribute [local instance] timeHilbert_secondCountable
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

def negativeTimeVector : TimeHilbert := intervalVector (-1) 0

def invisiblePolynomial : polynomialCylindricalDomain :=
  firstChaosPolynomial (hilbertEmbedding TimeHilbert negativeTimeVector)

def negativeField : TimeProbabilityL2 :=
  GaussianTimeProductL2.productTensor negativeTimeVector gaussianOne

theorem invisiblePolynomial_norm_sq : ‖(invisiblePolynomial : GaussianL2)‖ ^ 2 = 1 := by
  rw [invisiblePolynomial, GaussianTimeSensitivity.firstChaosPolynomial_norm,
    (hilbertEmbedding TimeHilbert).norm_map, ← real_inner_self_eq_norm_sq,
    negativeTimeVector, intervalVector_inner, inter_self]
  norm_num [Measure.real, Real.volume_Ioc]

theorem invisiblePolynomial_centered :
    (∫ ω, (invisiblePolynomial : GaussianL2) ω ∂gaussianProduct) = 0 := by
  unfold invisiblePolynomial
  rw [integral_congr_ae (firstChaosPolynomial_coeFn
    (hilbertEmbedding TimeHilbert negativeTimeVector))]
  exact firstChaos_integral _

theorem invisiblePolynomial_derivative :
    polynomialDerivative invisiblePolynomial = fieldEmbedding negativeField := by
  rw [negativeField, fieldEmbedding_tensor]
  apply Lp.ext
  filter_upwards [firstChaosPolynomial_derivative_coeFn
    (hilbertEmbedding TimeHilbert negativeTimeVector),
    scalarTensor_coeFn (hilbertEmbedding TimeHilbert negativeTimeVector) gaussianOne,
    gaussianOne_coeFn] with ω hd hs h1
  change polynomialDerivative invisiblePolynomial ω = _ at hd
  rw [hd, hs, h1, one_smul]

theorem negativeField_orthogonal (u : fullPredictable) :
    inner ℝ negativeField (u : TimeProbabilityL2) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  have ht := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp
      (intervalVector_coeFn (-1) 0)
  filter_upwards [GaussianTimeProductL2.productTensor_coeFn negativeTimeVector gaussianOne,
    ht, ((mem_fullPredictable_iff u).mp u.property).2] with z hf ht hu
  change negativeField z = negativeTimeVector z.1 * gaussianOne z.2 at hf
  change negativeTimeVector z.1 = (Ioc (-1 : ℝ) 0).indicator (fun _ => 1) z.1 at ht
  by_cases hz : z ∈ positiveTimes
  · have hp : 0 < z.1 := hz.1
    have hn : z.1 ∉ Ioc (-1 : ℝ) 0 := fun h => (not_le_of_gt hp) h.2
    rw [hf, ht, indicator_of_notMem hn, zero_mul]
    simp
  · rw [hu hz]
    simp

theorem invisiblePolynomial_predictableAdjoint :
    predictableAdjoint (invisiblePolynomial : GaussianL2) = 0 := by
  have h := predictableAdjoint_eq_projected_derivative
    ⟨(invisiblePolynomial : GaussianL2), closedCylindricalDerivative_core_mem invisiblePolynomial⟩
  rw [closedCylindricalDerivative_core_apply, invisiblePolynomial_derivative] at h
  change predictableAdjoint (invisiblePolynomial : GaussianL2) =
    predictableProjection (fieldEmbedding negativeField) at h
  rw [h]
  apply ext_inner_right ℝ
  intro u
  change inner ℝ (predictableField.toContinuousLinearMap.adjoint
    (fieldEmbedding negativeField)) u = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (fieldEmbedding negativeField) (fieldEmbedding (u : TimeProbabilityL2)) = _
  rw [fieldEmbedding.inner_map_map, negativeField_orthogonal]
  simp

theorem invisiblePolynomial_not_representable :
    (invisiblePolynomial : GaussianL2) ∉ itoIntegral.toLinearMap.range := by
  rintro ⟨u, hu⟩
  change itoIntegral u = (invisiblePolynomial : GaussianL2) at hu
  have hzero : u = 0 := by
    rw [← predictableAdjoint_integral u, hu, invisiblePolynomial_predictableAdjoint]
  have hf : (invisiblePolynomial : GaussianL2) = 0 := by
    rw [← hu, hzero, map_zero]
  have hn := invisiblePolynomial_norm_sq
  rw [hf, norm_zero, zero_pow (by decide)] at hn
  norm_num at hn

/-- A rigorous scope obstruction to ambient all-centered-L2 predictable representation. -/
theorem exists_centered_not_representable : ∃ F : GaussianL2,
    (∫ ω, F ω ∂gaussianProduct) = 0 ∧ ‖F‖ ^ 2 = 1 ∧
      F ∉ itoIntegral.toLinearMap.range :=
  ⟨invisiblePolynomial, invisiblePolynomial_centered, invisiblePolynomial_norm_sq,
    invisiblePolynomial_not_representable⟩

end OperatorDerivativeRewrite.Foundation.GaussianAmbientRepresentationObstruction
