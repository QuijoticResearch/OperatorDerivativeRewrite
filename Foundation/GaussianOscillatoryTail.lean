import Foundation.RiemannQuarticGaussianTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
/-! Signed complex Gaussian tails with norm-of-curvature control.
Integration by parts retains cancellation even when Re(b) is small relative
to norm(b). These are Gaussian-model estimates, not actual Xi tail estimates. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianOscillatoryTail

theorem inverse_square_integrable (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => (x^2)⁻¹) (Ioi r) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hr
  norm_num [Real.rpow_neg,Real.rpow_two] at h
  exact h

theorem inverse_square_integral (r : ℝ) (hr : 0 < r) :
    (∫ x : ℝ in Ioi r, (x^2)⁻¹)=r⁻¹ := by
  have h := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hr
  norm_num [Real.rpow_neg,Real.rpow_two,Real.rpow_neg_one] at h
  exact h

theorem gaussian_norm_le_one (b : ℂ) (hb : 0 ≤ b.re) (x : ℝ) :
    ‖Complex.exp (-b*(x : ℂ)^2)‖ ≤ 1 := by
  rw [norm_cexp_neg_mul_sq]
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])

theorem weighted_integrable (b : ℂ) (hb : 0 ≤ b.re) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => Complex.exp (-b*(x : ℂ)^2)/(x : ℂ)^2) (Ioi r) := by
  apply (inverse_square_integrable r hr).mono' ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hr.trans hx)
    exact ((by fun_prop : ContinuousAt (fun x : ℝ => Complex.exp (-b*(x : ℂ)^2)) x).div
      (by fun_prop) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hx0))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    exact (div_le_div_of_nonneg_right (gaussian_norm_le_one b hb x) (sq_nonneg x)).trans_eq (one_div _)

theorem weighted_norm_bound (b : ℂ) (hb : 0 ≤ b.re) (r : ℝ) (hr : 0 < r) :
    ‖∫ x : ℝ in Ioi r, Complex.exp (-b*(x : ℂ)^2)/(x : ℂ)^2‖ ≤ r⁻¹ := by
  calc
    _ ≤ ∫ x : ℝ in Ioi r, ‖Complex.exp (-b*(x : ℂ)^2)/(x : ℂ)^2‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Ioi r, (x^2)⁻¹ := by
      apply setIntegral_mono_on (weighted_integrable b hb r hr).norm
        (inverse_square_integrable r hr) measurableSet_Ioi
      intro x hx
      rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      exact (div_le_div_of_nonneg_right (gaussian_norm_le_one b hb x) (sq_nonneg x)).trans_eq (one_div _)
    _ = _ := inverse_square_integral r hr

theorem boundary_tendsto_zero (b : ℂ) (hb : 0 ≤ b.re) :
    Tendsto (fun x : ℝ => Complex.exp (-b*(x : ℂ)^2)/(x : ℂ)) atTop (nhds 0) := by
  apply squeeze_zero_norm' _ tendsto_inv_atTop_zero
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx]
  exact (div_le_div_of_nonneg_right (gaussian_norm_le_one b hb x) hx.le).trans_eq (one_div _)

theorem tail_integration_by_parts (b : ℂ) (hb : 0 < b.re) (r : ℝ) (hr : 0 < r) :
    (2*b)*(∫ x : ℝ in Ioi r, Complex.exp (-b*(x : ℂ)^2))=
      Complex.exp (-b*(r : ℂ)^2)/(r : ℂ)-
        (∫ x : ℝ in Ioi r, Complex.exp (-b*(x : ℂ)^2)/(x : ℂ)^2) := by
  have hd (x : ℝ) (hx : x ∈ Ici r) :
      HasDerivAt (fun y : ℝ => Complex.exp (-b*(y : ℂ)^2)/(y : ℂ))
        (-(2*b)*Complex.exp (-b*(x : ℂ)^2)-Complex.exp (-b*(x : ℂ)^2)/(x : ℂ)^2) x := by
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hr.trans_le hx))
    have h := (((((hasDerivAt_id x).ofReal_comp).pow 2).const_mul (-b)).cexp).div
      (hasDerivAt_id x).ofReal_comp hx0
    convert h using 1
    · funext y; rfl
    · simp only [id_eq,Pi.pow_apply,Complex.ofReal_one ]
      field_simp
      ring
  have hi := ((integrable_cexp_neg_mul_sq hb).integrableOn.const_mul (-(2*b))).sub
    (weighted_integrable b hb.le r hr)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi (boundary_tendsto_zero b hb.le)
  rw [integral_sub ((integrable_cexp_neg_mul_sq hb).integrableOn.const_mul (-(2*b)))
    (weighted_integrable b hb.le r hr), integral_const_mul] at h
  linear_combination -h

theorem tail_norm_bound (b : ℂ) (hb : 0 < b.re) (r : ℝ) (hr : 0 < r) :
    ‖∫ x : ℝ in Ioi r, Complex.exp (-b*(x : ℂ)^2)‖ ≤ 1/(‖b‖*r) := by
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have h := congrArg norm (tail_integration_by_parts b hb r hr)
  rw [norm_mul, norm_mul,Complex.norm_ofNat] at h
  have ht := norm_sub_le (Complex.exp (-b*(r : ℂ)^2)/(r : ℂ))
    (∫ x : ℝ in Ioi r, Complex.exp (-b*(x : ℂ)^2)/(x : ℂ)^2)
  have hfirst : ‖Complex.exp (-b*(r : ℂ)^2)/(r : ℂ)‖ ≤ r⁻¹ := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact (div_le_div_of_nonneg_right (gaussian_norm_le_one b hb.le r) hr.le).trans_eq (one_div _)
  have htail := weighted_norm_bound b hb.le r hr
  have hprod : (‖b‖*r)*(1/(‖b‖*r))=1 := by field_simp
  apply (le_div_iff₀ (mul_pos hbn hr)).mpr
  have hi : r*r⁻¹=1 := by field_simp
  nlinarith

theorem full_minus_truncated_bound (b : ℂ) (hb : 0 < b.re) (r : ℝ) (hr : 0 < r) :
    ‖(∫ x : ℝ, Complex.exp (-b*(x : ℂ)^2))-
      (∫ x : ℝ in -r..r, Complex.exp (-b*(x : ℂ)^2))‖ ≤
      2/(‖b‖*r) := by
  let f := fun x : ℝ => Complex.exp (-b*(x : ℂ)^2)
  have hi := integrable_cexp_neg_mul_sq hb
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := -r) (f := f) hi.integrableOn hi.integrableOn
  have hmiddle := intervalIntegral.integral_interval_add_Ioi
    (a := -r) (b := r) (f := f) hi.integrableOn hi.integrableOn
  have hleft : (∫ x : ℝ in Iic (-r), f x)=(∫ x : ℝ in Ioi r, f x) := by
    simpa only [f,Complex.ofReal_neg,neg_sq] using (integral_comp_neg_Ioi r f).symm
  have he : (∫ x : ℝ, f x)-(∫ x : ℝ in -r..r, f x)=
      (∫ x : ℝ in Ioi r, f x)+(∫ x : ℝ in Ioi r, f x) := by
    linear_combination -hsplit -hmiddle +hleft
  change ‖(∫ x : ℝ, f x)-(∫ x : ℝ in -r..r, f x)‖ ≤ _
  rw [he]
  have ht := tail_norm_bound b hb r hr
  change ‖∫ x : ℝ in Ioi r, f x‖ ≤ _ at ht
  calc
    _ ≤ ‖∫ x : ℝ in Ioi r, f x‖+‖∫ x : ℝ in Ioi r, f x‖ := norm_add_le _ _
    _ ≤ 2*(1/(‖b‖*r)) := by linarith
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.GaussianOscillatoryTail
