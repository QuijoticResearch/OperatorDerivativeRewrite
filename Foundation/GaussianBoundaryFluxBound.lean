import Foundation.CoerciveMovingBoundary

/-! Quantitative repair of the moving Gaussian cutoff term with an explicit radius margin. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.GaussianBoundaryFluxBound
set_option backward.isDefEq.respectTransparency false
open CoerciveMovingBoundary

theorem numerator_nonneg (c r : ℝ) (hr : 0 < r) : 0 ≤ numerator c r := by
  apply intervalIntegral.integral_nonneg (by linarith)
  intro y _
  exact mul_nonneg (sq_nonneg y) (weight_pos c y).le

theorem gap_le (c r : ℝ) (hr : 0 < r) : gap c r ≤ r^2*normalizer c r := by
  unfold gap
  linarith [numerator_nonneg c r hr]

theorem central_weight_lower (c r y : ℝ) (hc : 0 ≤ c)
    (hy : y ∈ Icc (-r/2) (r/2)) : Real.exp (-c*r^2/4) ≤ weight c y := by
  apply Real.exp_le_exp.mpr
  have hs : 0 ≤ (r/2-y)*(r/2+y) := mul_nonneg (by linarith [hy.2]) (by linarith [hy.1])
  have hsq : 0 ≤ r^2/4-y^2 := by nlinarith
  have hp := mul_nonneg hc hsq
  nlinarith

/-- Integrating only the central half-window gives a useful exponential lower bound. -/
theorem normalizer_lower (c r : ℝ) (hc : 0 ≤ c) (hr : 0 < r) :
    r*Real.exp (-c*r^2/4) ≤ normalizer c r := by
  have hw : Continuous (weight c) := by unfold weight; fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (a := -r/2) (b := r/2) (by linarith)
    (continuous_const.intervalIntegrable _ _) (hw.intervalIntegrable _ _)
    (fun y hy => central_weight_lower c r y hc hy)
  have hs := intervalIntegral.integral_mono_interval (μ := volume) (a := -r/2) (b := r/2)
    (c := -r) (d := r) (by linarith) (by linarith) (by linarith)
    (Filter.Eventually.of_forall fun y => (weight_pos c y).le) (hw.intervalIntegrable _ _)
  have he : (∫ y in (-r/2)..(r/2), Real.exp (-c*r^2/4))=r*Real.exp (-c*r^2/4) := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [he] at hi
  exact hi.trans hs

theorem endpoint_ratio_bound (c r : ℝ) (hc : 0 ≤ c) (hr : 0 < r) :
    r*weight c r/normalizer c r ≤ Real.exp (-3*c*r^2/4) := by
  have hz := normalizer_lower c r hc hr
  have hp : 0 < r*Real.exp (-c*r^2/4) := mul_pos hr (Real.exp_pos _)
  have hd := div_le_div_of_nonneg_left (mul_nonneg hr.le (weight_pos c r).le) hp hz
  have he : r*weight c r/(r*Real.exp (-c*r^2/4))=Real.exp (-3*c*r^2/4) := by
    rw [mul_div_mul_left _ _ hr.ne', weight, ← Real.exp_sub]
    congr 1
    ring
  exact hd.trans_eq he

theorem boundarySlope_abs (c x : ℝ) (hx : x^2 < 1) :
    |boundarySlope c x|=2*|x| *weight c (radius x)*gap c (radius x)/
      (radius x*(normalizer c (radius x))^2) := by
  have hr := radius_pos x hx
  have hz := normalizer_pos c (radius x) hr
  have hg := gap_pos c (radius x) hr
  have hw := weight_pos c (radius x)
  simp only [boundarySlope, abs_mul, abs_div, abs_neg, abs_pow,
    abs_of_pos hr, abs_of_pos hz, abs_of_pos hg, abs_of_pos hw]
  norm_num
  field_simp

theorem boundarySlope_crude (c x : ℝ) (hx : x^2 < 1) :
    |boundarySlope c x| ≤ 2*|x| *radius x*weight c (radius x)/normalizer c (radius x) := by
  have hr := radius_pos x hx
  have hz := normalizer_pos c (radius x) hr
  rw [boundarySlope_abs c x hx]
  calc
    _ ≤ 2*|x| *weight c (radius x)*((radius x)^2*normalizer c (radius x))/
        (radius x*(normalizer c (radius x))^2) := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left (gap_le c (radius x) hr)
          (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg x)) (weight_pos c _).le)
      · positivity
    _ = _ := by field_simp

theorem boundarySlope_exponential (c x : ℝ) (hc : 0 ≤ c) (hx : x^2 < 1) :
    |boundarySlope c x| ≤ 2*|x| *Real.exp (-3*c*(radius x)^2/4) := by
  have he := mul_le_mul_of_nonneg_left (endpoint_ratio_bound c (radius x) hc (radius_pos x hx))
    (show 0 ≤ 2*|x| by positivity)
  have hid : 2*|x| *radius x*weight c (radius x)/normalizer c (radius x)=
      (2*|x|)*(radius x*weight c (radius x)/normalizer c (radius x)) := by ring
  exact (boundarySlope_crude c x hx).trans (by simpa only [← hid] using he)

theorem strict_subcorridor_bound (c x ρ : ℝ) (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hx : x^2 < 1) (hmargin : ρ ≤ radius x) :
    |boundarySlope c x| ≤ 2*Real.exp (-3*c*ρ^2/4) := by
  have hr := radius_pos x hx
  have hs : ρ^2 ≤ (radius x)^2 := (sq_le_sq₀ hρ.le hr.le).mpr hmargin
  have hp := mul_le_mul_of_nonneg_left hs hc
  have he : Real.exp (-3*c*(radius x)^2/4) ≤ Real.exp (-3*c*ρ^2/4) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have ha : |x| ≤ 1 := (sq_le_sq₀ (abs_nonneg x) (by norm_num : (0:ℝ) ≤ 1)).mp
    (by rw [sq_abs]; linarith)
  calc
    _ ≤ 2*|x| *Real.exp (-3*c*(radius x)^2/4) := boundarySlope_exponential c x hc hx
    _ ≤ 2*Real.exp (-3*c*(radius x)^2/4) := by
      nlinarith [mul_le_mul_of_nonneg_right ha (Real.exp_pos (-3*c*(radius x)^2/4)).le]
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by norm_num)

theorem full_derivative_exponential (a c x : ℝ) (hc : 0 ≤ c) (hx : x^2 < 1) :
    |deriv (fullSquareMean a c) x| ≤ 2*|x| *Real.exp (-3*c*(radius x)^2/4) := by
  have he : fullSquareMean a c=corridorMean c := funext (fullSquareMean_eq a c)
  rw [he, (corridorMean_hasDerivAt c x hx).deriv]
  exact boundarySlope_exponential c x hc hx

theorem full_derivative_subcorridor (a c x ρ : ℝ) (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hx : x^2 < 1) (hmargin : ρ ≤ radius x) :
    |deriv (fullSquareMean a c) x| ≤ 2*Real.exp (-3*c*ρ^2/4) := by
  have he : fullSquareMean a c=corridorMean c := funext (fullSquareMean_eq a c)
  rw [he, (corridorMean_hasDerivAt c x hx).deriv]
  exact strict_subcorridor_bound c x ρ hc hρ hx hmargin

theorem exponential_tolerance (c ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hscale : 4*Real.log (2/ε)/(3*ρ^2) ≤ c) :
    2*Real.exp (-3*c*ρ^2/4) ≤ ε := by
  have hs := (div_le_iff₀ (by positivity : 0 < 3*ρ^2)).mp hscale
  have he : -3*c*ρ^2/4 ≤ -Real.log (2/ε) := by nlinarith
  have hp : 0 < (2:ℝ)/ε := div_pos (by norm_num) hε
  have hi : 2*Real.exp (-Real.log (2/ε))=ε := by
    rw [Real.exp_neg, Real.exp_log hp]
    field_simp
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num)).trans_eq hi

theorem full_derivative_tolerance (a c x ρ ε : ℝ) (hc : 0 ≤ c) (hρ : 0 < ρ) (hε : 0 < ε)
    (hx : x^2 < 1) (hmargin : ρ ≤ radius x)
    (hscale : 4*Real.log (2/ε)/(3*ρ^2) ≤ c) :
    |deriv (fullSquareMean a c) x| ≤ ε :=
  (full_derivative_subcorridor a c x ρ hc hρ hx hmargin).trans (exponential_tolerance c ρ ε hρ hε hscale)

end OperatorDerivativeRewrite.Foundation.GaussianBoundaryFluxBound
