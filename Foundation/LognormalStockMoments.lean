import Foundation.GaussianDoubleExponential
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact power-integrability boundary for an independent Gaussian random-volatility proxy. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.LognormalStockMoments
set_option backward.isDefEq.respectTransparency false
abbrev γ := GaussianCore.γ
abbrev law : Measure (ℝ × ℝ) := γ.prod γ

def stock (a : ℝ) (w : ℝ × ℝ) : ℝ :=
  Real.exp (Real.exp (a*w.1)*w.2-(Real.exp (a*w.1))^2/2)

theorem stock_pos (a : ℝ) (w : ℝ × ℝ) : 0 < stock a w := Real.exp_pos _

theorem power_factor (a q x z : ℝ) :
    (stock a (x,z))^q = Real.exp (-(q*(Real.exp (a*x))^2)/2) *
      Real.exp ((q*Real.exp (a*x))*z) := by
  simp only [stock, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

theorem power_fiber_integrable (a q x : ℝ) :
    Integrable (fun z : ℝ => (stock a (x,z))^q) γ := by
  simp_rw [power_factor]
  exact (GaussianDoubleExponential.integrable_exp_linear _).const_mul _

theorem gaussian_exp_integral (t : ℝ) :
    (∫ z : ℝ, Real.exp (t*z) ∂γ) = Real.exp (t^2/2) := by
  have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) t
  simpa [mgf] using h

theorem power_fiber_integral (a q x : ℝ) :
    (∫ z : ℝ, (stock a (x,z))^q ∂γ) =
      Real.exp ((q*(q-1)/2)*(Real.exp (a*x))^2) := by
  simp_rw [power_factor]
  rw [integral_const_mul, gaussian_exp_integral, ← Real.exp_add]
  congr 1
  ring

theorem power_norm_fiber_integral (a q x : ℝ) :
    (∫ z : ℝ, ‖(stock a (x,z))^q‖ ∂γ) =
      Real.exp ((q*(q-1)/2)*(Real.exp (a*x))^2) := by
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (stock_pos a _) q)] using
    power_fiber_integral a q x

theorem power_continuous (a q : ℝ) : Continuous (fun w => (stock a w)^q) := by
    have he : (fun w : ℝ × ℝ => (stock a w)^q) =
        (fun w => Real.exp ((Real.exp (a*w.1)*w.2-(Real.exp (a*w.1))^2/2)*q)) := by
      funext w
      exact (Real.exp_mul _ _).symm
    rw [he]
    fun_prop

theorem power_integrable_iff_variance_exp (a q : ℝ) :
    Integrable (fun w => (stock a w)^q) law ↔
      Integrable (fun x : ℝ => Real.exp ((q*(q-1)/2)*(Real.exp (a*x))^2)) γ := by
  rw [integrable_prod_iff (power_continuous a q).aestronglyMeasurable]
  simp_rw [power_norm_fiber_integral]
  exact and_iff_right (Filter.Eventually.of_forall (power_fiber_integrable a q))

theorem power_integrable_iff {a : ℝ} (ha : 0 < a) (q : ℝ) :
    Integrable (fun w => (stock a w)^q) law ↔ 0 ≤ q ∧ q ≤ 1 := by
  rw [power_integrable_iff_variance_exp]
  constructor
  · intro hi
    have hn : q*(q-1)/2 ≤ 0 := by
      by_contra h
      exact GaussianDoubleExponential.not_integrable_exp_lognormal_square ha
        (lt_of_not_ge h) hi
    constructor <;> nlinarith
  · rintro ⟨hq0,hq1⟩
    have hc : q*(q-1)/2 ≤ 0 := by nlinarith
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg _))

theorem stock_integrable (a : ℝ) : Integrable (stock a) law := by
  have h : Integrable (fun w => (stock a w)^(1 : ℝ)) law := by
    rw [power_integrable_iff_variance_exp]
    simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) γ)
  simpa using h

theorem stock_mean (a : ℝ) : (∫ w, stock a w ∂law) = 1 := by
  rw [integral_prod _ (stock_integrable a)]
  have hf (x : ℝ) : (∫ z, stock a (x,z) ∂γ) = 1 := by
    simpa using power_fiber_integral a 1 x
  simp_rw [hf]
  simp

theorem not_integrable_higher_power {a q : ℝ} (ha : 0 < a) (hq : 1 < q) :
    ¬ Integrable (fun w => (stock a w)^q) law := by
  rw [power_integrable_iff ha]
  exact fun h => (not_le_of_gt hq) h.2

theorem higher_moment_infinite {a q : ℝ} (ha : 0 < a) (hq : 1 < q) :
    (∫⁻ w, ENNReal.ofReal ((stock a w)^q) ∂law) = ∞ := by
  by_contra h
  apply not_integrable_higher_power ha hq
  refine ⟨(power_continuous a q).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun w =>
    (Real.rpow_pos_of_pos (stock_pos a w) q).le)).mpr
  exact lt_top_iff_ne_top.mpr h

end OperatorDerivativeRewrite.Foundation.LognormalStockMoments
