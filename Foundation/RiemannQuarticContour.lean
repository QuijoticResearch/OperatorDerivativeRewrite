import Foundation.RiemannQuarticFrequencyBranch
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
/-! Actual signed contour shift for the arithmetic quartic Xi integrand.
A uniform thin-strip tail kills the right vertical segment. The half-line
identity retains the left vertical integral exactly, with its sign. For Re(z)>=0
that endpoint is bounded without dividing by z, including z=0. Relative to
any actual real global amplitude maximum it is bounded by a fixed constant
 times exp(-t/2). No Gaussian normalization or integrated saddle remainder
relative to the frequency-dependent dominant saddle is asserted. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Interval
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticContour
open RiemannQuarticFrequencyBranch RiemannQuarticSaddleNeighborhood RiemannThetaComplexKernel

theorem thin_strip_domain (w : ℂ) (hw : |w.im| ≤ 1/16) : 0 < (Complex.exp (4*w)).re := by
  have hb : w ∈ closedBall (w.re : ℂ) (1/16) := by
    rw [mem_closedBall,dist_eq_norm]
    have he : w-(w.re : ℂ)=(w.im : ℂ)*Complex.I := by apply Complex.ext <;> simp
    rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    exact hw
  have h := exp_complex_real_lower w.re w hb
  linarith [Real.exp_pos (4*w.re)]

theorem weight_analyticAt (t : ℝ) (z w : ℂ) (hw : |w.im| ≤ 1/16) :
    AnalyticAt ℂ (saddleWeight t z) w := by
  have h : AnalyticAt ℂ (fun v : ℂ => Complex.exp ((t : ℂ)*v^4+Complex.I*z*v)) w := by fun_prop
  exact h.mul (kernelComplex_analyticAt w (thin_strip_domain w hw))

theorem finite_rectangle_identity (t L h : ℝ) (z : ℂ) (hh : 0 ≤ h) (hh1 : h ≤ 1/16) :
    (∫ x : ℝ in 0..L, saddleWeight t z (x : ℂ))-
    (∫ x : ℝ in 0..L, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I))+
    Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((L : ℂ)+(y : ℂ)*Complex.I))-
    Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I))=0 := by
  have hd : DifferentiableOn ℂ (saddleWeight t z)
      ([[((0 : ℂ)).re,((L : ℂ)+(h : ℂ)*Complex.I).re]] ×ℂ
        [[((0 : ℂ)).im,((L : ℂ)+(h : ℂ)*Complex.I).im]]) := by
    intro w hw
    have hwi : w.im ∈ Icc 0 h := by
      simpa [mem_reProdIm,uIcc_of_le hh] using hw.2
    have him : |w.im| ≤ 1/16 := by rw [abs_of_nonneg hwi.1]; exact hwi.2.trans hh1
    exact (weight_analyticAt t z w him).differentiableAt.differentiableWithinAt
  have hc := integral_boundary_rect_eq_zero_of_differentiableOn (saddleWeight t z)
    0 ((L : ℂ)+(h : ℂ)*Complex.I) hd
  simpa [Complex.real_smul] using hc


theorem thin_strip_ball (w : ℂ) (hw : |w.im| ≤ 1/16) :
    w ∈ closedBall (w.re : ℂ) (1/16) := by
  rw [mem_closedBall,dist_eq_norm]
  have he : w-(w.re : ℂ)=(w.im : ℂ)*Complex.I := by apply Complex.ext <;> simp
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact hw

theorem kernel_strip_norm_bound (w : ℂ) (ha : 0 ≤ w.re) (hw : |w.im| ≤ 1/16) :
    ‖kernelComplex w‖ ≤ 5676*Real.exp (9*w.re)*Real.exp (-(Real.pi/2)*Real.exp (4*w.re)) := by
  have hb := thin_strip_ball w hw
  have hr := exp_complex_real_lower w.re w hb
  have hv : 1 ≤ Real.exp (4*w.re) := Real.one_le_exp_iff.mpr (by linarith)
  have hr0 : 0 ≤ (Complex.exp (4*w)).re := by linarith
  have hrel := relative_bound w (by linarith) (by linarith : 1/2 ≤ (Complex.exp (4*w)).re)
  have he : Real.exp (-3*Real.pi*(Complex.exp (4*w)).re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  have ht := norm_add_le (kernelComplex w-leading w) (leading w)
  rw [sub_add_cancel] at ht
  have hp := mul_le_mul_of_nonneg_right he (norm_nonneg (leading w))
  have hn : ‖kernelComplex w‖ ≤ 129*‖leading w‖ := by nlinarith
  have hlead := leading_norm_upper w (by linarith)
  have hdecay : Real.exp (-Real.pi*(Complex.exp (4*w)).re) ≤
      Real.exp (-(Real.pi/2)*Real.exp (4*w.re)) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hr Real.pi_pos.le
    linarith
  calc
    _ ≤ 129*‖leading w‖ := hn
    _ ≤ 129*(44*Real.exp (9*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re)) := by gcongr
    _ ≤ 129*(44*Real.exp (9*w.re)*Real.exp (-(Real.pi/2)*Real.exp (4*w.re))) := by gcongr
    _ = _ := by ring

theorem weight_strip_norm_bound (t : ℝ) (z w : ℂ) (ha : 1 ≤ w.re) (hw : |w.im| ≤ 1/16) :
    ‖saddleWeight t z w‖ ≤ 5676*Real.exp
      (16*|t| *w.re^4+(2*‖z‖+9)*w.re-(Real.pi/2)*Real.exp (4*w.re)) := by
  have hb := thin_strip_ball w hw
  have hd : ‖w-(w.re : ℂ)‖ ≤ (1/16 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hb
  have hn := norm_add_le (w-(w.re : ℂ)) (w.re : ℂ)
  rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ w.re)] at hn
  have hnorm : ‖w‖ ≤ 2*w.re := by linarith
  have hpow : ‖w‖^4 ≤ 16*w.re^4 := by
    calc
      _ ≤ (2*w.re)^4 := pow_le_pow_left₀ (norm_nonneg w) hnorm 4
      _ = _ := by ring
  have hre := Complex.re_le_norm ((t : ℂ)*w^4+Complex.I*z*w)
  have htriangle := norm_add_le ((t : ℂ)*w^4) (Complex.I*z*w)
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,one_mul] at htriangle
  have hp1 := mul_le_mul_of_nonneg_left hpow (abs_nonneg t)
  have hp2 := mul_le_mul_of_nonneg_left hnorm (norm_nonneg z)
  have he : ((t : ℂ)*w^4+Complex.I*z*w).re ≤ 16*|t| *w.re^4+2*‖z‖*w.re := by
    nlinarith
  rw [saddleWeight,norm_mul,Complex.norm_exp]
  calc
    _ ≤ Real.exp (16*|t| *w.re^4+2*‖z‖*w.re)*
      (5676*Real.exp (9*w.re)*Real.exp (-(Real.pi/2)*Real.exp (4*w.re))) :=
      mul_le_mul (Real.exp_le_exp.mpr he) (kernel_strip_norm_bound w (by linarith) hw)
        (norm_nonneg _) (Real.exp_pos _).le
    _ = 5676*(Real.exp (16*|t| *w.re^4+2*‖z‖*w.re)*Real.exp (9*w.re)*
        Real.exp (-(Real.pi/2)*Real.exp (4*w.re))) := by ring
    _ = _ := by rw [← Real.exp_add,← Real.exp_add]; congr 2 <;> ring

theorem eventually_uniform_strip_decay (t : ℝ) (z : ℂ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ h : ℝ, |h| ≤ 1/16 →
      ‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖ ≤ 5676*Real.exp (-x) := by
  filter_upwards [RiemannQuarticDomain.quartic_exponent_dominated (32*|t|) (4*‖z‖+20),
    Filter.eventually_ge_atTop (1 : ℝ)] with x he hx
  intro h hh
  have hw : |(((x : ℂ)+(h : ℂ)*Complex.I)).im| ≤ 1/16 := by simpa using hh
  have hbound := weight_strip_norm_bound t z ((x : ℂ)+(h : ℂ)*Complex.I) (by simpa using hx) hw
  try simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.ofReal_im,
    Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at hbound
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  linarith [mul_pos Real.pi_pos (Real.exp_pos (4*x))]


theorem eventually_right_segment_bound (t : ℝ) (z : ℂ) :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ h : ℝ, 0 ≤ h → h ≤ 1/16 →
      ‖∫ y : ℝ in 0..h, saddleWeight t z ((L : ℂ)+(y : ℂ)*Complex.I)‖ ≤
        (5676*Real.exp (-L))*h := by
  filter_upwards [eventually_uniform_strip_decay t z] with L hL
  intro h hh hh1
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := h) (C := 5676*Real.exp (-L))
    (fun y hy => hL y (by
      rw [uIoc_of_le hh] at hy
      rw [abs_of_nonneg hy.1.le]
      exact hy.2.trans hh1))
  simpa only [sub_zero,abs_of_nonneg hh] using he

theorem right_segment_tendsto_zero (t : ℝ) (z : ℂ) (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1/16) :
    Filter.Tendsto (fun L : ℝ => ∫ y : ℝ in 0..h,
      saddleWeight t z ((L : ℂ)+(y : ℂ)*Complex.I)) Filter.atTop (nhds 0) := by
  have he : Filter.Tendsto (fun L : ℝ => (5676*Real.exp (-L))*h) Filter.atTop (nhds 0) := by
    have hx := Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot
    simpa using (hx.const_mul (5676 : ℝ)).mul_const h
  apply squeeze_zero_norm' _ he
  filter_upwards [eventually_right_segment_bound t z] with L hL
  exact hL h hh hh1


theorem shifted_weight_continuous (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| ≤ 1/16) :
    Continuous (fun x : ℝ => saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have ha := weight_analyticAt t z ((x : ℂ)+(h : ℂ)*Complex.I) (by simpa using hh)
  have hc : ContinuousAt (fun y : ℝ => (y : ℂ)+(h : ℂ)*Complex.I) x := by fun_prop
  exact ContinuousAt.comp (f := fun y : ℝ => (y : ℂ)+(h : ℂ)*Complex.I)
    (g := saddleWeight t z) ha.continuousAt hc

theorem shifted_weight_integrable (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| ≤ 1/16) :
    IntegrableOn (fun x : ℝ => saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)) (Ioi 0) := by
  have hc := shifted_weight_continuous t z h hh
  have ho : (fun x : ℝ => saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)) =O[atTop]
      (fun x : ℝ => Real.exp (-x)) := by
    apply Asymptotics.IsBigO.of_bound 5676
    filter_upwards [eventually_uniform_strip_decay t z] with x hx
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hx h hh
  have hi : IntegrableOn (fun x : ℝ => saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)) (Ici 0) :=
    (hc.continuousOn.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop ho
      ⟨Ioi 1,Ioi_mem_atTop 1,by simpa only [neg_one_mul] using exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ)<1)⟩
  exact hi.mono_set Ioi_subset_Ici_self

theorem halfline_contour_shift (t : ℝ) (z : ℂ) (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1/16) :
    (∫ x : ℝ in Ioi 0, saddleWeight t z (x : ℂ))=
      (∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I))+
        Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)) := by
  have h0 : IntegrableOn (fun x : ℝ => saddleWeight t z (x : ℂ)) (Ioi 0) := by
    simpa using shifted_weight_integrable t z 0 (by norm_num)
  have hhabs : |h| ≤ 1/16 := by rwa [abs_of_nonneg hh]
  have ha := intervalIntegral_tendsto_integral_Ioi 0 h0 tendsto_id
  have hb := intervalIntegral_tendsto_integral_Ioi 0 (shifted_weight_integrable t z h hhabs) tendsto_id
  have hr := (right_segment_tendsto_zero t z h hh hh1).const_mul Complex.I
  have hl : Tendsto (fun _ : ℝ => Complex.I*(∫ y : ℝ in 0..h,
      saddleWeight t z ((y : ℂ)*Complex.I))) atTop
      (nhds (Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)))) := tendsto_const_nhds
  have hlim := ((ha.sub hb).add hr).sub hl
  have heq : (fun L : ℝ =>
      (∫ x : ℝ in 0..L, saddleWeight t z (x : ℂ))-
      (∫ x : ℝ in 0..L, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I))+
      Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((L : ℂ)+(y : ℂ)*Complex.I))-
      Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I))) =ᶠ[atTop]
        (fun _ => (0 : ℂ)) := Eventually.of_forall (fun L => finite_rectangle_identity t L h z hh hh1)
  have hc := hlim.congr' heq
  have he := tendsto_nhds_unique hc (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (nhds 0))
  simp only [mul_zero,add_zero] at he
  linear_combination he


theorem kernel_imaginary_axis_bound (y : ℝ) (hy : |y| ≤ 1/16) :
    ‖kernelComplex ((y : ℂ)*Complex.I)‖ ≤ 5676 := by
  have h := kernel_strip_norm_bound ((y : ℂ)*Complex.I) (by simp) (by simpa using hy)
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,
    mul_zero,zero_mul,sub_zero,Real.exp_zero,mul_one] at h
  have he : Real.exp (-(Real.pi/2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
  nlinarith

theorem imaginary_weight_norm_bound (t : ℝ) (z : ℂ) (h y : ℝ)
    (hh : 0 ≤ h) (hh1 : h ≤ 1/16) (hy : y ∈ Icc 0 h) (hz : 0 ≤ z.re) :
    ‖saddleWeight t z ((y : ℂ)*Complex.I)‖ ≤ 5676*Real.exp (|t| *h^4) := by
  have hkernel := kernel_imaginary_axis_bound y (by rw [abs_of_nonneg hy.1]; exact hy.2.trans hh1)
  have he : ((t : ℂ)*((y : ℂ)*Complex.I)^4+Complex.I*z*((y : ℂ)*Complex.I)).re=t*y^4-z.re*y := by
    simp only [mul_pow,Complex.I_sq,show Complex.I^4=(1 : ℂ) by norm_num [pow_succ,Complex.I_sq],
      mul_one,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,← Complex.ofReal_pow]
    ring
  have hp := pow_le_pow_left₀ hy.1 hy.2 4
  have ht := mul_le_mul_of_nonneg_right (le_abs_self t) (pow_nonneg hy.1 4)
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg t)
  have hexp : t*y^4-z.re*y ≤ |t| *h^4 := by nlinarith [mul_nonneg hz hy.1]
  rw [saddleWeight,norm_mul,Complex.norm_exp,he]
  calc
    _ ≤ Real.exp (|t| *h^4)*5676 := mul_le_mul (Real.exp_le_exp.mpr hexp) hkernel (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

theorem left_segment_bound (t : ℝ) (z : ℂ) (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1/16)
    (hz : 0 ≤ z.re) :
    ‖∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)‖ ≤
      (5676*Real.exp (|t| *h^4))*h := by
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := h) (C := 5676*Real.exp (|t| *h^4))
    (fun y hy => imaginary_weight_norm_bound t z h y hh hh1 (by
      rw [uIoc_of_le hh] at hy
      exact ⟨hy.1.le,hy.2⟩) hz)
  simpa only [sub_zero,abs_of_nonneg hh] using he


open RiemannQuarticDomain RiemannQuarticKernel RiemannQuarticRealSaddle

theorem max_amplitude_lower (t u : ℝ)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) :
    Real.exp t*kernel 1 ≤ weighted 0 t 0 u := by
  have h := hm (by norm_num : (1 : ℝ) ∈ Ici 0)
  change weighted 0 t 0 1 ≤ weighted 0 t 0 u at h
  simpa only [weighted,pow_zero,one_mul,zero_mul,add_zero,one_pow,mul_one] using h

theorem left_segment_relative_peak_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) (z : ℂ) (hz : 0 ≤ z.re)
    (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1/16) :
    ‖∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)‖/weighted 0 t 0 u ≤
      (5676/(16*kernel 1))*Real.exp (-t/2) := by
  have hleft := left_segment_bound t z h hh hh1 hz
  rw [abs_of_nonneg ht] at hleft
  have hpeak := max_amplitude_lower t u hm
  have hk : 0 < kernel 1 := kernel_pos 1 (by norm_num)
  have hbase : 0 < Real.exp t*kernel 1 := mul_pos (Real.exp_pos _) hk
  have hpeakpos := weighted_pos t u hu
  have hnum : ‖∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)‖ ≤
      (5676/16)*Real.exp (t*h^4) := by
    have hp := mul_le_mul_of_nonneg_left hh1 (by positivity : 0 ≤ 5676*Real.exp (t*h^4))
    nlinarith
  have hp : h^4 ≤ (1/2 : ℝ) := by
    calc
      _ ≤ (1/16 : ℝ)^4 := pow_le_pow_left₀ hh hh1 4
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

end OperatorDerivativeRewrite.Foundation.RiemannQuarticContour
