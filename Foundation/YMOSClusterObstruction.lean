import Foundation.SU2PositiveChannelObstruction
import Foundation.YMReflectionPositiveShift
/-! Counterexamples to two OS clustering steps in a Yang–Mills manuscript. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation.SU2CoupledLoopResponse
namespace OperatorDerivativeRewrite.Foundation.YMObservableScaleObstruction

def scaledCov (r s : ℝ) : ℝ :=
  (∫ p, (s * F p) * G p ∂coupledLaw r) -
    (∫ p, s * F p ∂coupledLaw r) * (∫ p, G p ∂coupledLaw r)

theorem scaledCov_eq (r s : ℝ) : scaledCov r s = s * corr r := by
  have hprod : (∫ p, (s * F p) * G p ∂coupledLaw r) =
      s * (∫ p, X p ∂coupledLaw r) := by
    have hpoint (p) : (s * F p) * G p = s * X p := by simp [X]; ring
    simp_rw [hpoint]
    rw [integral_const_mul]
  rw [scaledCov, hprod, integral_const_mul, corr_eq_covariance]
  ring

theorem no_uniform_constant (r t m : ℝ) (hc : 0 < corr r) :
    ¬ ∃ C : ℝ, ∀ s : ℝ, |scaledCov r s| ≤ C * Real.exp (-m*t) := by
  rintro ⟨C, hC⟩
  let D : ℝ := C * Real.exp (-m*t)
  have hD : 0 ≤ D := by
    simpa [D, scaledCov_eq] using hC 0
  have h := hC ((D+1)/corr r)
  rw [scaledCov_eq] at h
  have hval : ((D+1)/corr r) * corr r = D+1 := by
    field_simp
  rw [hval, abs_of_nonneg (by linarith)] at h
  dsimp [D] at h
  linarith

theorem arbitrarily_small_coupling_no_uniform_constant (ε t m : ℝ) (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r < ε ∧
      ¬ ∃ C : ℝ, ∀ s : ℝ, |scaledCov r s| ≤ C * Real.exp (-m*t) := by
  obtain ⟨r, hr, hrε, hc⟩ := positive_corr_near_zero ε hε
  exact ⟨r, hr, hrε, no_uniform_constant r t m hc⟩
open OperatorDerivativeRewrite.Foundation.YMReflectionPositiveShift

theorem reflected_vs_unreflected (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    reflectedCov s (s+t) < stationaryCov t := by
  rw [reflected_factor s (s+t) hs.le (by linarith)]
  simp only [stationaryCov, abs_of_nonneg ht]
  rw [← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  linarith

end OperatorDerivativeRewrite.Foundation.YMObservableScaleObstruction
