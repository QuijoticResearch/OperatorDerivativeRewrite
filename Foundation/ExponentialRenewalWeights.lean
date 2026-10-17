import Foundation.ExponentialHoldingSequence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The exponential renewal weights are derived by an actual convolution integral. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace OperatorDerivativeRewrite.Foundation.ExponentialRenewalWeights

def weight (n : ℕ) (t : ℝ) : ℝ :=
  if 0 ≤ t then Real.exp (-t) * t^n / n.factorial else 0

theorem weight_measurable (n : ℕ) : Measurable (weight n) := by
  unfold weight
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    (by fun_prop) measurable_const

theorem base_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂ExponentialHoldingSequence.base) =
      ∫ x, (if 0 ≤ x then Real.exp (-x) else 0) * f x := by
  unfold ExponentialHoldingSequence.base expMeasure gammaMeasure gammaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_gammaPDFReal 1 1).ennreal_ofReal)
    (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    have hn : 0 ≤ gammaPDFReal 1 1 x :=
      gammaPDFReal_nonneg (by norm_num) (by norm_num) x
    change (ENNReal.ofReal (gammaPDFReal 1 1 x)).toReal * f x = _
    rw [ENNReal.toReal_ofReal hn]
    simp only [gammaPDFReal, Real.one_rpow, Real.Gamma_one, div_one,
      sub_self, Real.rpow_zero, mul_one, one_mul])

theorem weight_convolution (n : ℕ) (t : ℝ) :
    (∫ x, weight n (t-x) ∂ExponentialHoldingSequence.base) = weight (n+1) t := by
  rw [base_integral]
  by_cases ht : 0 ≤ t
  · have he : (fun x : ℝ => (if 0 ≤ x then Real.exp (-x) else 0) * weight n (t-x)) =
        (Icc 0 t).indicator (fun x => Real.exp (-t) / n.factorial * (t-x)^n) := by
      funext x
      by_cases hx : 0 ≤ x
      · by_cases hxt : x ≤ t
        · have hin : x ∈ Icc (0 : ℝ) t := ⟨hx,hxt⟩
          rw [ite_eq_left hx, weight, ite_eq_left (sub_nonneg.mpr hxt),
            indicator_of_mem hin]
          have hex : Real.exp (-x) * Real.exp (-(t-x)) = Real.exp (-t) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc
            _ = (Real.exp (-x) * Real.exp (-(t-x))) / n.factorial * (t-x)^n := by ring
            _ = _ := by rw [hex]
        · rw [ite_eq_left hx, weight, ite_eq_right (by linarith), mul_zero,
            indicator_of_notMem (by simp only [mem_Icc, not_and_or]; exact Or.inr hxt)]
      · rw [ite_eq_right hx, zero_mul, indicator_of_notMem (by
          simp only [mem_Icc, not_and_or]; exact Or.inl hx)]
    rw [he, integral_indicator measurableSet_Icc, integral_const_mul,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^n) t,
      sub_self, sub_zero, integral_pow,
      zero_pow (Nat.succ_ne_zero n), sub_zero, weight, ite_eq_left ht,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · have he : (fun x : ℝ => (if 0 ≤ x then Real.exp (-x) else 0) * weight n (t-x)) = 0 := by
      funext x
      by_cases hx : 0 ≤ x
      · simp only [ite_eq_left hx, weight, ite_eq_right (show ¬ 0 ≤ t-x by linarith),
          mul_zero, Pi.zero_apply]
      · simp only [ite_eq_right hx, zero_mul, Pi.zero_apply]
    rw [he]
    change (∫ x : ℝ, (0 : ℝ)) = _
    simp only [integral_zero, weight, ite_eq_right ht]

end OperatorDerivativeRewrite.Foundation.ExponentialRenewalWeights
