import Foundation.GaussianCore
import Mathlib.Tactic
import Mathlib.Probability.Moments.IntegrableExpMul

/-! A Gaussian volatility proxy has every power moment, but its positive exponential does not. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace OperatorDerivativeRewrite.Foundation.GaussianDoubleExponential
set_option backward.isDefEq.respectTransparency false

theorem exponential_dominates_square {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    {x : ℝ} (hx : 6 / (c*a^3) ≤ x) : x^2 ≤ c * Real.exp (a*x) := by
  have hd : 0 < c*a^3 := by positivity
  have hx0 : 0 ≤ x := le_trans (by positivity : 0 ≤ 6 / (c*a^3)) hx
  have hlin : 6 ≤ c*a^3*x := by simpa [mul_comm] using (div_le_iff₀ hd).mp hx
  have hpow := mul_le_mul_of_nonneg_right hlin (sq_nonneg x)
  have he := mul_le_mul_of_nonneg_left
    (Real.pow_div_factorial_le_exp (a*x) (mul_nonneg ha.le hx0) 3) hc.le
  norm_num at he
  nlinarith

theorem density_product_lower {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    {x : ℝ} (hx : 6 / (c*a^3) ≤ x) :
    (Real.sqrt (2*Real.pi))⁻¹ ≤
      gaussianPDFReal 0 1 x * Real.exp (c * Real.exp (a*x)) := by
  have h := exponential_dominates_square ha hc hx
  have hexp : 1 ≤ Real.exp (-(x^2)/2+c*Real.exp (a*x)) := by
    apply Real.one_le_exp_iff.mpr
    nlinarith [sq_nonneg x]
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [mul_assoc, ← Real.exp_add]
  exact le_mul_of_one_le_right (by positivity) hexp

theorem not_integrable_double_exp {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ¬ Integrable (fun x : ℝ => Real.exp (c*Real.exp (a*x))) GaussianCore.γ := by
  intro hi
  have hd := GaussianCore.integrable_density_mul hi
  let R := 6 / (c*a^3)
  let k := (Real.sqrt (2*Real.pi))⁻¹
  have hk : 0 < k := by dsimp [k]; positivity
  have hconst : IntegrableOn (fun _ : ℝ => k) (Ici R) volume := by
    apply hd.integrableOn.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    simpa only [Real.norm_eq_abs, abs_of_pos hk] using density_product_lower ha hc hx
  have hf := (integrableOn_const_iff (by finiteness)).mp hconst
  have hnonpos : k ≤ 0 := by
    simpa [Real.enorm_eq_ofReal_abs, abs_of_pos hk, hk.ne', Real.volume_Ici] using hf
  exact (not_le_of_gt hk) hnonpos

theorem integrable_exp_linear (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a*x)) GaussianCore.γ :=
  integrable_exp_mul_gaussianReal a

theorem integrable_exp_abs (r : ℝ) :
    Integrable (fun x : ℝ => Real.exp (r*|x|)) GaussianCore.γ :=
  integrable_exp_mul_abs (integrable_exp_linear r) (integrable_exp_linear (-r))

theorem integrable_lognormal_rpow (a r : ℝ) :
    Integrable (fun x : ℝ => (Real.exp (a*x))^r) GaussianCore.γ := by
  simpa only [← Real.exp_mul, mul_right_comm a _ r, mul_comm a r] using
    integrable_exp_linear (r*a)

theorem integrable_lognormal_power (a : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => (Real.exp (a*x))^n) GaussianCore.γ := by
  simpa [Real.exp_nat_mul, mul_assoc] using integrable_exp_linear ((n : ℝ)*a)

theorem not_integrable_exp_lognormal_square {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ¬ Integrable (fun x : ℝ => Real.exp (c*(Real.exp (a*x))^2)) GaussianCore.γ := by
  have he (x : ℝ) : (Real.exp (a*x))^2 = Real.exp ((2*a)*x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [he] using not_integrable_double_exp (mul_pos (by norm_num) ha) hc

end OperatorDerivativeRewrite.Foundation.GaussianDoubleExponential
