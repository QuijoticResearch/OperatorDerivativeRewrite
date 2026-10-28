import Foundation.YMContinuumCorrelationScaling
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
/-! A positive reflected one-particle kernel whose translated norm is strictly smaller. -/
noncomputable section
open Finset
namespace OperatorDerivativeRewrite.Foundation.YMReflectionPositiveShift

def stationaryCov (u : ℝ) : ℝ := Real.exp (-|u|)
def reflectedCov (s t : ℝ) : ℝ := stationaryCov (s+t)

theorem reflected_factor (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    reflectedCov s t = Real.exp (-s) * Real.exp (-t) := by
  simp [reflectedCov, stationaryCov, abs_of_nonneg (add_nonneg hs ht), ← Real.exp_add]
  ring

theorem reflected_psd (n : ℕ) (times c : Fin n → ℝ) (ht : ∀ i, 0 ≤ times i) :
    0 ≤ ∑ i, ∑ j, c i * c j * reflectedCov (times i) (times j) := by
  have he : (∑ i, ∑ j, c i * c j * reflectedCov (times i) (times j)) =
      (∑ i, c i * Real.exp (-times i)) ^ 2 := by
    simp_rw [reflected_factor _ _ (ht _) (ht _)]
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  positivity

theorem reflected_norm_strict (t : ℝ) (ht : 0 < t) :
    reflectedCov t t < reflectedCov 0 0 := by
  rw [reflected_factor t t ht.le ht.le, reflected_factor 0 0 le_rfl le_rfl]
  have he : Real.exp (-t) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  simp only [neg_zero, Real.exp_zero, one_mul]
  nlinarith [Real.exp_pos (-t)]

end OperatorDerivativeRewrite.Foundation.YMReflectionPositiveShift
