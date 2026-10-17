import Foundation.GaussianConditionalLikelihoodRoot
import Foundation.GaussianTiltFiniteHorizon
import Foundation.GaussianDeterminantConditional

/-! Exact conditional projection error and future predictable energy of the likelihood root. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianLikelihoodRootInnovation
open InfiniteGaussian GaussianTimeProcess GaussianCore GaussianCriticalExponential
open GaussianTiltL2Domain GaussianTiltBrownianDomain GaussianConditionalLikelihoodRoot
open GaussianConditionalIto GaussianConditionalClarkOcone GaussianPredictableAdjoint
open GaussianPredictableCutoff GaussianDeterminantConditional
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

theorem norm_square_integral (F : InfiniteGaussian.GaussianL2) :
    ‖F‖^2 = ∫ ω, F ω ^ 2 ∂gaussianProduct := by
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp [pow_two]

theorem terminal_norm_square : ‖terminalValue‖^2 = 1 := by
  have he : (∫ ω, rootDensity ω ^ 2 ∂gaussianProduct) = 1 := by
    have h := ofReal_integral_eq_lintegral_ofReal rootDensity_memLp_P.integrable_sq
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (rootDensity ω)))
    rw [rootDensity_square_lintegral_P] at h
    have hn := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun ω => sq_nonneg (rootDensity ω))),
      ENNReal.toReal_one] using hn
  rw [norm_square_integral, ← he]
  apply integral_congr_ae
  filter_upwards [terminalValue_coeFn] with ω hω
  rw [hω]

theorem projection_coeFn : pastProjection 1 terminalValue =ᵐ[gaussianProduct] meanPast :=
  (pastProjection_ae 1 terminalValue).trans
    ((condExp_congr_ae (m := naturalFiltration 1) terminalValue_coeFn).trans rootDensity_condExp)

theorem meanPast_square (ω : SampleSpace) :
    meanPast ω ^ 2 = Real.exp (-(1/4 : ℝ)*(process 1 ω)^2) := by
  rw [meanPast_eq, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem meanPast_square_integral_squared :
    (∫ ω, meanPast ω ^ 2 ∂gaussianProduct)^2 = (2/3 : ℝ) := by
  have hm : Measurable (fun x : ℝ => Real.exp (-(1/4 : ℝ)*x^2)) := by fun_prop
  have h := (process_hasLaw 1).integral_comp hm.aestronglyMeasurable
  change (∫ ω, Real.exp (-(1/4 : ℝ)*(process 1 ω)^2) ∂gaussianProduct) = _ at h
  simp_rw [meanPast_square]
  rw [h, square_laplace_squared _ (by norm_num)]
  norm_num

theorem projection_norm_square :
    ‖pastProjection 1 terminalValue‖^2 = Real.sqrt (2/3 : ℝ) := by
  have he : ‖pastProjection 1 terminalValue‖^2 = ∫ ω, meanPast ω ^ 2 ∂gaussianProduct := by
    rw [norm_square_integral]
    apply integral_congr_ae
    filter_upwards [projection_coeFn] with ω hω
    rw [hω]
  rw [he]
  rw [← meanPast_square_integral_squared, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (integral_nonneg (fun ω => sq_nonneg (meanPast ω)))]

theorem conditional_error_exact :
    ‖terminalValue - pastProjection 1 terminalValue‖^2 = 1 - Real.sqrt (2/3 : ℝ) := by
  have h := (pastL2 1).norm_sq_eq_add_norm_sq_starProjection terminalValue
  rw [Submodule.starProjection_orthogonal_val] at h
  change ‖terminalValue‖^2 = ‖pastProjection 1 terminalValue‖^2 +
    ‖terminalValue - pastProjection 1 terminalValue‖^2 at h
  rw [terminal_norm_square, projection_norm_square] at h
  linarith

theorem future_energy_exact :
    ‖predictableAdjoint terminalValue -
      predictableCut 1 (predictableAdjoint terminalValue)‖^2 =
        1 - Real.sqrt (2/3 : ℝ) := by
  rw [← conditional_variance_identity 1 terminalValue terminalValue_brownian]
  exact conditional_error_exact

end OperatorDerivativeRewrite.Foundation.GaussianLikelihoodRootInnovation
