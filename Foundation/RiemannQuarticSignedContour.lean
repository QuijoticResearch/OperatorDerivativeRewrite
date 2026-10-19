import Foundation.RiemannQuarticSaddleGeometry
/-! Signed upward/downward contour shifts for the actual quartic kernel.
The finite rectangle and vanishing right segment allow either sign of height.
At an actual nearby saddle, Re(z)*Im(w)>=0, so the vertical endpoint is bounded
in both directions. Bounds use absolute height and retain the signed integral.
No parity assumption on the complex kernel is introduced. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Interval
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticSignedContour
open RiemannQuarticContour RiemannQuarticFrequencyBranch RiemannQuarticSaddleBranch
open RiemannQuarticSaddleGeometry RiemannQuarticSaddleTimes RiemannQuarticSaddleNeighborhood
open RiemannQuarticQuantitativeSaddle RiemannQuarticCurvature
open RiemannQuarticDomain RiemannQuarticKernel RiemannQuarticRealSaddle

theorem vertical_abs_le (h y : ℝ) (hy : y ∈ uIcc 0 h) : |y| ≤ |h| := by
  rcases le_total 0 h with hh | hh
  · rw [uIcc_of_le hh] at hy
    rw [abs_of_nonneg hy.1,abs_of_nonneg hh]
    exact hy.2
  · rw [uIcc_of_ge hh] at hy
    rw [abs_of_nonpos hy.2,abs_of_nonpos hh]
    linarith [hy.1]

theorem finite_rectangle_signed (t L h : ℝ) (z : ℂ) (hh : |h| ≤ 1/16) :
    (∫ x : ℝ in 0..L, saddleWeight t z (x : ℂ))-
    (∫ x : ℝ in 0..L, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I))+
    Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((L : ℂ)+(y : ℂ)*Complex.I))-
    Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I))=0 := by
  have hd : DifferentiableOn ℂ (saddleWeight t z)
      ([[((0 : ℂ)).re,((L : ℂ)+(h : ℂ)*Complex.I).re]] ×ℂ
        [[((0 : ℂ)).im,((L : ℂ)+(h : ℂ)*Complex.I).im]]) := by
    intro w hw
    have hwi : w.im ∈ uIcc 0 h := by
      simpa [mem_reProdIm] using hw.2
    have him : |w.im| ≤ 1/16 := (vertical_abs_le h w.im hwi).trans hh
    exact (weight_analyticAt t z w him).differentiableAt.differentiableWithinAt
  have hc := integral_boundary_rect_eq_zero_of_differentiableOn (saddleWeight t z)
    0 ((L : ℂ)+(h : ℂ)*Complex.I) hd
  simpa [Complex.real_smul] using hc

theorem eventually_right_segment_signed (t : ℝ) (z : ℂ) :
    ∀ᶠ L : ℝ in atTop, ∀ h : ℝ, |h| ≤ 1/16 →
      ‖∫ y : ℝ in 0..h, saddleWeight t z ((L : ℂ)+(y : ℂ)*Complex.I)‖ ≤
        (5676*Real.exp (-L))*|h| := by
  filter_upwards [eventually_uniform_strip_decay t z] with L hL
  intro h hh
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := h) (C := 5676*Real.exp (-L))
    (fun y hy => hL y ((vertical_abs_le h y (uIoc_subset_uIcc hy)).trans hh))
  simpa only [sub_zero] using he

theorem right_segment_signed_tendsto_zero (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| ≤ 1/16) :
    Tendsto (fun L : ℝ => ∫ y : ℝ in 0..h,
      saddleWeight t z ((L : ℂ)+(y : ℂ)*Complex.I)) atTop (nhds 0) := by
  have he : Tendsto (fun L : ℝ => (5676*Real.exp (-L))*|h|) atTop (nhds 0) := by
    have hx := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    simpa using (hx.const_mul (5676 : ℝ)).mul_const |h|
  apply squeeze_zero_norm' _ he
  filter_upwards [eventually_right_segment_signed t z] with L hL
  exact hL h hh

theorem halfline_contour_shift_signed (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| ≤ 1/16) :
    (∫ x : ℝ in Ioi 0, saddleWeight t z (x : ℂ))=
      (∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I))+
        Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)) := by
  have h0 : IntegrableOn (fun x : ℝ => saddleWeight t z (x : ℂ)) (Ioi 0) := by
    simpa using shifted_weight_integrable t z 0 (by norm_num)
  have hhabs : |h| ≤ 1/16 := hh
  have ha := intervalIntegral_tendsto_integral_Ioi 0 h0 tendsto_id
  have hb := intervalIntegral_tendsto_integral_Ioi 0 (shifted_weight_integrable t z h hhabs) tendsto_id
  have hr := (right_segment_signed_tendsto_zero t z h hh).const_mul Complex.I
  have hl : Tendsto (fun _ : ℝ => Complex.I*(∫ y : ℝ in 0..h,
      saddleWeight t z ((y : ℂ)*Complex.I))) atTop
      (nhds (Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)))) := tendsto_const_nhds
  have hlim := ((ha.sub hb).add hr).sub hl
  have heq : (fun L : ℝ =>
      (∫ x : ℝ in 0..L, saddleWeight t z (x : ℂ))-
      (∫ x : ℝ in 0..L, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I))+
      Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((L : ℂ)+(y : ℂ)*Complex.I))-
      Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I))) =ᶠ[atTop]
        (fun _ => (0 : ℂ)) := Eventually.of_forall (fun L => finite_rectangle_signed t L h z hh)
  have hc := hlim.congr' heq
  have he := tendsto_nhds_unique hc (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (nhds 0))
  simp only [mul_zero,add_zero] at he
  linear_combination he

theorem stationary_saddle_height_nonpos (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (z w : ℂ) (hz : z.re ≤ 0)
    (hw : w ∈ closedBall (u : ℂ) (1/102400)) (he : complexSlope t w= -(Complex.I*z)) :
    w.im ≤ 0 := by
  have hd : ∀ v ∈ closedBall (u : ℂ) (1/102400), DifferentiableAt ℂ (complexSlope t) v := by
    intro v hv
    exact (slope_analytic_on_neighborhood t u hu v
      (closedBall_subset_closedBall (by norm_num) hv)).differentiableAt
  have hb := stationary_slope_deriv_near_center t u ht hu hs
  have h := scalar_linearization_bound (complexSlope t) (u : ℂ)
    (deriv (complexSlope t) (u : ℂ)) (1/102400)
    (‖deriv (complexSlope t) (u : ℂ)‖/2) hd hb w (w.re : ℂ) hw (real_projection_mem u w _ hw)
  have hneg := stationary_phaseSlope_deriv_neg t u ht hu hs
  rw [slope_deriv_real t u (by linarith),he,complexSlope_real] at h
  have hnorm : ‖w-(w.re : ℂ)‖=|w.im| := by
    have hh : w-(w.re : ℂ)=(w.im : ℂ)*Complex.I := by apply Complex.ext <;> simp
    rw [hh,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  rw [hnorm,Complex.norm_real,Real.norm_eq_abs,abs_of_neg hneg] at h
  have him := Complex.abs_im_le_norm
    (-(Complex.I*z)-(phaseSlope t w.re : ℂ)-((deriv (phaseSlope t) u : ℝ) : ℂ)*(w-(w.re : ℂ)))
  have hle := him.trans h
  simp only [Complex.sub_im,Complex.neg_im,Complex.mul_re,Complex.mul_im,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,zero_add,one_mul,
    add_zero,sub_zero] at hle
  by_contra hn
  have hwpos : 0 < w.im := lt_of_not_ge hn
  rw [abs_of_pos hwpos] at hle
  have hleft := le_abs_self (-z.re-deriv (phaseSlope t) u*w.im)
  nlinarith

theorem stationary_saddle_height_product (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (z w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/102400)) (he : complexSlope t w= -(Complex.I*z)) :
    0 ≤ z.re*w.im := by
  rcases le_total 0 z.re with hz | hz
  · exact mul_nonneg hz (stationary_saddle_height_nonneg t u ht hu hs z w hz hw he)
  · exact mul_nonneg_of_nonpos_of_nonpos hz (stationary_saddle_height_nonpos t u ht hu hs z w hz hw he)

theorem vertical_product_nonneg (x h y : ℝ) (hy : y ∈ uIcc 0 h) (hprod : 0 ≤ x*h) :
    0 ≤ x*y := by
  rcases lt_trichotomy h 0 with hh | hh | hh
  · rw [uIcc_of_ge hh.le] at hy
    have hx : x ≤ 0 := by nlinarith
    exact mul_nonneg_of_nonpos_of_nonpos hx hy.2
  · subst h
    have hy0 : y=0 := by simpa using hy
    simp [hy0]
  · rw [uIcc_of_le hh.le] at hy
    have hx : 0 ≤ x := by nlinarith
    exact mul_nonneg hx hy.1

theorem imaginary_weight_signed_bound (t : ℝ) (z : ℂ) (h y : ℝ)
    (hh : |h| ≤ 1/16) (hy : y ∈ uIcc 0 h) (hz : 0 ≤ z.re*h) :
    ‖saddleWeight t z ((y : ℂ)*Complex.I)‖ ≤ 5676*Real.exp (|t| *h^4) := by
  have hya := vertical_abs_le h y hy
  have hkernel := kernel_imaginary_axis_bound y (hya.trans hh)
  have he : ((t : ℂ)*((y : ℂ)*Complex.I)^4+Complex.I*z*((y : ℂ)*Complex.I)).re=t*y^4-z.re*y := by
    simp only [mul_pow,Complex.I_sq,show Complex.I^4=(1 : ℂ) by norm_num [pow_succ,Complex.I_sq],
      mul_one,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,← Complex.ofReal_pow]
    ring
  have hp : y^4 ≤ h^4 := by
    simpa only [pow_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ y^4),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ h^4)] using pow_le_pow_left₀ (abs_nonneg y) hya 4
  have ht := mul_le_mul_of_nonneg_right (le_abs_self t) (by positivity : (0 : ℝ) ≤ y^4)
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg t)
  have hexp : t*y^4-z.re*y ≤ |t| *h^4 := by linarith [vertical_product_nonneg z.re h y hy hz]
  rw [saddleWeight,norm_mul,Complex.norm_exp,he]
  calc
    _ ≤ Real.exp (|t| *h^4)*5676 := mul_le_mul (Real.exp_le_exp.mpr hexp) hkernel (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

theorem left_segment_signed_bound (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| ≤ 1/16) (hz : 0 ≤ z.re*h) :
    ‖∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)‖ ≤
      (5676*Real.exp (|t| *h^4))*|h| := by
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := h) (C := 5676*Real.exp (|t| *h^4))
    (fun y hy => imaginary_weight_signed_bound t z h y hh (uIoc_subset_uIcc hy) hz)
  simpa only [sub_zero] using he

theorem left_segment_relative_peak_signed (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) (z : ℂ)
    (h : ℝ) (hh : |h| ≤ 1/16) (hz : 0 ≤ z.re*h) :
    ‖∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)‖/weighted 0 t 0 u ≤
      (5676/(16*kernel 1))*Real.exp (-t/2) := by
  have hleft := left_segment_signed_bound t z h hh hz
  rw [abs_of_nonneg ht] at hleft
  have hpeak := max_amplitude_lower t u hm
  have hk : 0 < kernel 1 := kernel_pos 1 (by norm_num)
  have hbase : 0 < Real.exp t*kernel 1 := mul_pos (Real.exp_pos _) hk
  have hpeakpos := weighted_pos t u hu
  have hnum : ‖∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)‖ ≤
      (5676/16)*Real.exp (t*h^4) := by
    have hp := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 5676*Real.exp (t*h^4))
    nlinarith
  have hp : h^4 ≤ (1/2 : ℝ) := by
    calc
      _ ≤ (1/16 : ℝ)^4 := by
        have hb := pow_le_pow_left₀ (abs_nonneg h) hh 4
        simpa only [pow_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ h^4)] using hb
      _ ≤ _ := by norm_num
  have hexp : Real.exp (t*(h^4-1)) ≤ Real.exp (-t/2) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hp ht
    linarith
  calc
    _ ≤ ((5676/16)*Real.exp (t*h^4))/weighted 0 t 0 u :=
      div_le_div_of_nonneg_right hnum hpeakpos.le
    _ ≤ ((5676/16)*Real.exp (t*h^4))/(Real.exp t*kernel 1) :=
      div_le_div_of_nonneg_left (by positivity) hbase hpeak
    _ = (5676/(16*kernel 1))*Real.exp (t*(h^4-1)) := by
      rw [show t*(h^4-1)=t*h^4-t by ring,Real.exp_sub]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticSignedContour
