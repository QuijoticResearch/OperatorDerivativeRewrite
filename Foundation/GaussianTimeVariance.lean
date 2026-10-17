import Foundation.LognormalStockMoments
import Foundation.CriticalLpSpike
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! An actual continuous-time rank-one Gaussian volatility example and Jensen obstruction. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.GaussianTimeVariance
set_option backward.isDefEq.respectTransparency false
abbrev timeLaw := CriticalLpSpike.unitLaw
abbrev γ := GaussianCore.γ

theorem continuous_time_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f timeLaw := by
  exact hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem time_mean : (∫ t : ℝ, t ∂timeLaw) = 1/2 := by
  change (∫ t in Ioc (0 : ℝ) 1, t) = _
  rw [← intervalIntegral.integral_of_le (by norm_num), integral_id]
  norm_num

theorem exp_integral_le {T : Type*} [MeasurableSpace T] {ν : Measure T}
    [IsProbabilityMeasure ν] {f : T → ℝ} (hf : Integrable f ν)
    (he : Integrable (fun t => Real.exp (f t)) ν) :
    Real.exp (∫ t, f t ∂ν) ≤ ∫ t, Real.exp (f t) ∂ν := by
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => mem_univ _) hf he

def volatility (a t x : ℝ) : ℝ := Real.exp (a*t*x)
def variance (a x : ℝ) : ℝ := ∫ t, volatility a t x ∂timeLaw

theorem volatility_time_integrable (a x : ℝ) :
    Integrable (fun t => volatility a t x) timeLaw :=
  continuous_time_integrable (by unfold volatility; fun_prop)

theorem volatility_square_time_integrable (a x : ℝ) :
    Integrable (fun t => (volatility a t x)^2) timeLaw :=
  continuous_time_integrable (by unfold volatility; fun_prop)

theorem variance_lower (a x : ℝ) : Real.exp ((a/2)*x) ≤ variance a x := by
  have h := exp_integral_le (ν := timeLaw)
    (f := fun t => a*t*x) (continuous_time_integrable (by fun_prop))
    (volatility_time_integrable a x)
  have hm : (∫ t : ℝ, a*t*x ∂timeLaw) = (a/2)*x := by
    rw [integral_mul_const, integral_const_mul, time_mean]
    ring
  simpa only [hm, variance, volatility] using h

theorem variance_pos (a x : ℝ) : 0 < variance a x :=
  lt_of_lt_of_le (Real.exp_pos _) (variance_lower a x)

theorem not_integrable_exp_variance {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ¬ Integrable (fun x => Real.exp (c*variance a x)) γ := by
  intro hi
  apply GaussianDoubleExponential.not_integrable_double_exp (a := a/2) (c := c)
    (div_pos ha (by norm_num)) hc
  apply hi.mono' (Continuous.aestronglyMeasurable (by fun_prop))
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (variance_lower a x) hc.le)

theorem integral_volatility_square (a x : ℝ) :
    (∫ t, (volatility a t x)^2 ∂timeLaw) = variance (2*a) x := by
  have he (t : ℝ) : (volatility a t x)^2 = volatility (2*a) t x := by
    rw [volatility, ← Real.exp_nat_mul, volatility]
    congr 1
    ring
  simp_rw [he]
  rfl

theorem not_integrable_exp_integrated_square {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ¬ Integrable (fun x => Real.exp (c*(∫ t, (volatility a t x)^2 ∂timeLaw))) γ := by
  simpa only [integral_volatility_square] using
    not_integrable_exp_variance (mul_pos (by norm_num) ha) hc

theorem volatility_power_integrable (a t r : ℝ) :
    Integrable (fun x => (volatility a t x)^r) γ :=
  GaussianDoubleExponential.integrable_lognormal_rpow (a*t) r

theorem volatility_power_integral (a t r : ℝ) :
    (∫ x, (volatility a t x)^r ∂γ) = Real.exp ((r*a*t)^2/2) := by
  have he (x : ℝ) : (volatility a t x)^r = Real.exp ((r*a*t)*x) := by
    rw [volatility, ← Real.exp_mul]
    congr 1
    ring
  simp_rw [he]
  exact LognormalStockMoments.gaussian_exp_integral _

theorem volatility_power_uniform_bound (a r : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x, (volatility a t x)^r ∂γ) ≤ Real.exp ((r*a)^2/2) := by
  rw [volatility_power_integral]
  apply Real.exp_le_exp.mpr
  have ht2 : t^2 ≤ 1 := by nlinarith [ht.1,ht.2]
  have hb := mul_le_mul_of_nonneg_left ht2 (sq_nonneg (r*a))
  nlinarith [show (r*a*t)^2 = (r*a)^2*t^2 by ring]

theorem driver_exp_abs_integrable (t r : ℝ) :
    Integrable (fun x : ℝ => Real.exp (r*|t*x|)) γ := by
  have hpos := GaussianDoubleExponential.integrable_exp_linear (r*t)
  have hneg := GaussianDoubleExponential.integrable_exp_linear (-(r*t))
  apply ProbabilityTheory.integrable_exp_mul_abs (X := fun x : ℝ => t*x)
  · simpa only [← mul_assoc] using hpos
  · simpa only [← mul_assoc, neg_mul] using hneg

theorem volatility_power_joint_integrable (a r : ℝ) :
    Integrable (fun w : ℝ × ℝ => (volatility a w.1 w.2)^r) (timeLaw.prod γ) := by
  have he (t x : ℝ) : (volatility a t x)^r = Real.exp ((a*t*x)*r) :=
    (Real.exp_mul _ _).symm
  have hm : AEStronglyMeasurable
      (fun w : ℝ × ℝ => (volatility a w.1 w.2)^r) (timeLaw.prod γ) := by
    simp_rw [he]
    exact Continuous.aestronglyMeasurable (by fun_prop)
  apply (integrable_prod_iff hm).mpr
  refine ⟨Filter.Eventually.of_forall fun t => volatility_power_integrable a t r, ?_⟩
  have hn (t x : ℝ) : ‖(volatility a t x)^r‖ = (volatility a t x)^r := by
    rw [he, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp_rw [hn, volatility_power_integral]
  apply (integrable_const (Real.exp ((r*a)^2/2))).mono'
    (Continuous.aestronglyMeasurable (by fun_prop))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa only [volatility_power_integral] using
    volatility_power_uniform_bound a r ⟨ht.1.le,ht.2⟩

theorem variance_integrable (a : ℝ) : Integrable (variance a) γ := by
  have hi := (volatility_power_joint_integrable a 1).integral_prod_right
  change Integrable (fun x => ∫ t, volatility a t x ∂timeLaw) γ
  simpa only [Real.rpow_one] using hi

theorem integrated_square_integrable (a : ℝ) :
    Integrable (fun x => ∫ t, (volatility a t x)^2 ∂timeLaw) γ := by
  simpa only [integral_volatility_square] using variance_integrable (2*a)

end OperatorDerivativeRewrite.Foundation.GaussianTimeVariance
