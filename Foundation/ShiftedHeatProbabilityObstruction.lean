import Foundation.MarkedTiltHeatLimit

/-! The shifted biharmonic symbol is not the characteristic function of a real probability law. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.ShiftedHeatProbabilityObstruction

theorem characteristic_norm_bound (μ : Measure ℝ) [IsProbabilityMeasure μ] (η : ℝ) :
    ‖∫ x, Complex.exp (Complex.I*(η : ℂ)*(x : ℂ)) ∂μ‖ ≤ 1 := by
  have hb : ∀ᵐ x : ℝ ∂μ, ‖Complex.exp (Complex.I*(η : ℂ)*(x : ℂ))‖ ≤ 1 := by
    filter_upwards with x
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  simpa using norm_integral_le_of_norm_le_const hb

theorem shifted_symbol_exceeds_one (s ξ : ℝ) (hs : 0 < s) (hξ : ξ ≠ 0) :
    1 < Real.exp (-s*((-ξ+ξ)^4-ξ^4)) := by
  rw [Real.one_lt_exp_iff]
  have hp : 0 < ξ^4 := by positivity
  simpa using mul_pos hs hp

theorem no_real_probability_shifted_symbol (s ξ : ℝ) (hs : 0 < s) (hξ : ξ ≠ 0)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ¬ ∀ η : ℝ, (∫ x, Complex.exp (Complex.I*(η : ℂ)*(x : ℂ)) ∂μ) =
      (Real.exp (-s*((η+ξ)^4-ξ^4)) : ℂ) := by
  intro h
  have hb := characteristic_norm_bound μ (-ξ)
  rw [h (-ξ), Complex.norm_real, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))] at hb
  exact (not_lt_of_ge hb) (shifted_symbol_exceeds_one s ξ hs hξ)

end OperatorDerivativeRewrite.Foundation.ShiftedHeatProbabilityObstruction
