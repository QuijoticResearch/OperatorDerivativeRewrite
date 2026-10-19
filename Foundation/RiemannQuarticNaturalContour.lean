import Foundation.RiemannQuarticKernelReflection
/-! Signed contour shifts through every closed substrip of |Imw|<pi/8.
The cutoff depends on the substrip's positive cosine margin. No uniform
estimate at the boundary and no far-field saddle dominance is asserted. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Interval
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticNaturalContour
open RiemannQuarticFrequencyBranch RiemannQuarticSaddleNeighborhood RiemannThetaComplexKernel
open RiemannQuarticKernelReflection RiemannQuarticSignedContour

theorem cosine_margin_pos (H : ℝ) (hH0 : 0 ≤ H) (hH : H < Real.pi/8) : 0 < Real.cos (4*H) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

theorem exp_real_lower (H : ℝ) (hH0 : 0 ≤ H) (hH : H < Real.pi/8)
    (w : ℂ) (hw : |w.im| ≤ H) :
    Real.cos (4*H)*Real.exp (4*w.re) ≤ (Complex.exp (4*w)).re := by
  have hab : |4*w.im| ≤ 4*H := by rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<4)]; linarith
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (4*w.im)) (by linarith : 4*H ≤ Real.pi) hab
  rw [Real.cos_abs] at hc
  have hm := mul_le_mul_of_nonneg_left hc (Real.exp_pos (4*w.re)).le
  simpa [Complex.exp_re,Complex.mul_re,Complex.mul_im,mul_comm] using hm

theorem kernel_norm_bound (w : ℂ) (ha : 0 ≤ w.re) (hR : 1/2 ≤ (Complex.exp (4*w)).re) :
    ‖kernelComplex w‖ ≤ 5676*Real.exp (9*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re) := by
  have hrel := relative_bound w ha hR
  have he : Real.exp (-3*Real.pi*(Complex.exp (4*w)).re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  have ht := norm_add_le (kernelComplex w-leading w) (leading w)
  rw [sub_add_cancel] at ht
  have hp := mul_le_mul_of_nonneg_right he (norm_nonneg (leading w))
  have hn : ‖kernelComplex w‖ ≤ 129*‖leading w‖ := by nlinarith
  have hl := leading_norm_upper w ha
  calc
    _ ≤ 129*‖leading w‖ := hn
    _ ≤ 129*(44*Real.exp (9*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re)) := by gcongr
    _ = _ := by ring

theorem weight_norm_bound (t : ℝ) (z : ℂ) (H : ℝ) (hH0 : 0 ≤ H) (hH : H < Real.pi/8)
    (w : ℂ) (ha : 1 ≤ w.re) (hw : |w.im| ≤ H) (hR : 1/2 ≤ (Complex.exp (4*w)).re) :
    ‖saddleWeight t z w‖ ≤ 5676*Real.exp
      (16*|t| *w.re^4+(2*‖z‖+9)*w.re-Real.pi*Real.cos (4*H)*Real.exp (4*w.re)) := by
  have hn := Complex.norm_le_abs_re_add_abs_im w
  rw [abs_of_nonneg (by linarith : 0 ≤ w.re)] at hn
  have hnorm : ‖w‖ ≤ 2*w.re := by linarith [Real.pi_lt_four]
  have hpow : ‖w‖^4 ≤ 16*w.re^4 := by
    calc
      _ ≤ (2*w.re)^4 := pow_le_pow_left₀ (norm_nonneg w) hnorm 4
      _ = _ := by ring
  have hre := Complex.re_le_norm ((t : ℂ)*w^4+Complex.I*z*w)
  have htriangle := norm_add_le ((t : ℂ)*w^4) (Complex.I*z*w)
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,one_mul] at htriangle
  have hp1 := mul_le_mul_of_nonneg_left hpow (abs_nonneg t)
  have hp2 := mul_le_mul_of_nonneg_left hnorm (norm_nonneg z)
  have he : ((t : ℂ)*w^4+Complex.I*z*w).re ≤ 16*|t| *w.re^4+2*‖z‖*w.re := by nlinarith
  have hE := exp_real_lower H hH0 hH w hw
  have hdec : Real.exp (-Real.pi*(Complex.exp (4*w)).re) ≤
      Real.exp (-Real.pi*Real.cos (4*H)*Real.exp (4*w.re)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  rw [saddleWeight,norm_mul,Complex.norm_exp]
  calc
    _ ≤ Real.exp (16*|t| *w.re^4+2*‖z‖*w.re)*
      (5676*Real.exp (9*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re)) :=
        mul_le_mul (Real.exp_le_exp.mpr he) (kernel_norm_bound w (by linarith) hR)
          (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (16*|t| *w.re^4+2*‖z‖*w.re)*
      (5676*Real.exp (9*w.re)*Real.exp (-Real.pi*Real.cos (4*H)*Real.exp (4*w.re))) := by gcongr
    _ = 5676*(Real.exp (16*|t| *w.re^4+2*‖z‖*w.re)*Real.exp (9*w.re)*
        Real.exp (-Real.pi*Real.cos (4*H)*Real.exp (4*w.re))) := by ring
    _ = _ := by rw [← Real.exp_add,← Real.exp_add]; congr 2 <;> ring

theorem eventually_uniform_decay (t : ℝ) (z : ℂ) (H : ℝ) (hH0 : 0 ≤ H) (hH : H < Real.pi/8) :
    ∀ᶠ x : ℝ in atTop, ∀ h : ℝ, |h| ≤ H →
      ‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖ ≤ 5676*Real.exp (-x) := by
  let c := Real.cos (4*H)
  have hc : 0 < c := cosine_margin_pos H hH0 hH
  filter_upwards [RiemannQuarticDomain.quartic_exponent_dominated (16*|t|/c) ((2*‖z‖+10)/c),
    eventually_ge_atTop (max 1 (1/c))] with x he hx
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hxc : 1/c ≤ x := (le_max_right _ _).trans hx
  have hcs : 1 ≤ c*x := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hxc
  have hExp : 1/2 ≤ c*Real.exp (4*x) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (4*x)) hc.le
    nlinarith
  intro h hh
  let w := (x : ℂ)+(h : ℂ)*Complex.I
  have hw : |w.im| ≤ H := by simpa only [w,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.ofReal_re,Complex.I_im,mul_one,Complex.I_re,mul_zero,add_zero,zero_add] using hh
  have hlow := exp_real_lower H hH0 hH w hw
  have hre : w.re=x := by simp [w]
  rw [hre] at hlow
  have hb := weight_norm_bound t z H hH0 hH w (by rwa [hre]) hw (hExp.trans hlow)
  rw [hre] at hb
  have hdom : 16*|t| *x^4+(2*‖z‖+10)*x ≤ Real.pi*c*Real.exp (4*x)/2 := by
    calc
      _ = c*((16*|t|/c)*x^4+((2*‖z‖+10)/c)*x) := by field_simp
      _ ≤ c*(Real.pi*Real.exp (4*x)/2) := mul_le_mul_of_nonneg_left he hc.le
      _ = _ := by ring
  apply hb.trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  change 16*|t| *x^4+(2*‖z‖+9)*x-Real.pi*c*Real.exp (4*x) ≤ -x
  nlinarith [mul_pos (mul_pos Real.pi_pos hc) (Real.exp_pos (4*x))]

theorem weight_analyticAt (t : ℝ) (z w : ℂ) (hw : |w.im| < Real.pi/8) :
    AnalyticAt ℂ (saddleWeight t z) w := by
  have ha : AnalyticAt ℂ (fun v : ℂ => Complex.exp ((t : ℂ)*v^4+Complex.I*z*v)) w := by fun_prop
  have hstrip : w ∈ strip := by
    change -Real.pi/8 < w.im ∧ w.im < Real.pi/8
    constructor <;> linarith [(abs_lt.mp hw).1,(abs_lt.mp hw).2]
  exact ha.mul (kernelComplex_analyticAt w (strip_domain w hstrip))

theorem finite_rectangle_signed (t L h : ℝ) (z : ℂ) (hh : |h| < Real.pi/8) :
    (∫ x : ℝ in 0..L, saddleWeight t z (x : ℂ))-
    (∫ x : ℝ in 0..L, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I))+
    Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((L : ℂ)+(y : ℂ)*Complex.I))-
    Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I))=0 := by
  have hd : DifferentiableOn ℂ (saddleWeight t z)
      ([[((0 : ℂ)).re,((L : ℂ)+(h : ℂ)*Complex.I).re]] ×ℂ
        [[((0 : ℂ)).im,((L : ℂ)+(h : ℂ)*Complex.I).im]]) := by
    intro w hw
    have hwi : w.im ∈ uIcc 0 h := by simpa [mem_reProdIm] using hw.2
    exact (weight_analyticAt t z w ((vertical_abs_le h w.im hwi).trans_lt hh)).differentiableAt.differentiableWithinAt
  have hc := integral_boundary_rect_eq_zero_of_differentiableOn (saddleWeight t z)
    0 ((L : ℂ)+(h : ℂ)*Complex.I) hd
  simpa [Complex.real_smul] using hc

theorem shifted_weight_continuous (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| < Real.pi/8) :
    Continuous (fun x : ℝ => saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have ha := weight_analyticAt t z ((x : ℂ)+(h : ℂ)*Complex.I) (by simpa using hh)
  have hc : ContinuousAt (fun y : ℝ => (y : ℂ)+(h : ℂ)*Complex.I) x := by fun_prop
  exact ContinuousAt.comp (f := fun y : ℝ => (y : ℂ)+(h : ℂ)*Complex.I)
    (g := saddleWeight t z) ha.continuousAt hc

theorem shifted_weight_integrable (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| < Real.pi/8) :
    IntegrableOn (fun x : ℝ => saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)) (Ioi 0) := by
  have hc := shifted_weight_continuous t z h hh
  have ho : (fun x : ℝ => saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)) =O[atTop]
      (fun x : ℝ => Real.exp (-x)) := by
    apply Asymptotics.IsBigO.of_bound 5676
    filter_upwards [eventually_uniform_decay t z |h| (abs_nonneg h) hh] with x hx
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hx h (le_refl _)
  have hi : IntegrableOn (fun x : ℝ => saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)) (Ici 0) :=
    (hc.continuousOn.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop ho
      ⟨Ioi 1,Ioi_mem_atTop 1,by simpa only [neg_one_mul] using exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ)<1)⟩
  exact hi.mono_set Ioi_subset_Ici_self

theorem right_segment_tendsto_zero (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| < Real.pi/8) :
    Tendsto (fun L : ℝ => ∫ y : ℝ in 0..h,
      saddleWeight t z ((L : ℂ)+(y : ℂ)*Complex.I)) atTop (nhds 0) := by
  have he : Tendsto (fun L : ℝ => (5676*Real.exp (-L))*|h|) atTop (nhds 0) := by
    have hx := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    simpa using (hx.const_mul (5676 : ℝ)).mul_const |h|
  apply squeeze_zero_norm' _ he
  filter_upwards [eventually_uniform_decay t z |h| (abs_nonneg h) hh] with L hL
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := h) (C := 5676*Real.exp (-L))
    (fun y hy => hL y (vertical_abs_le h y (uIoc_subset_uIcc hy)))
  simpa only [sub_zero] using hb

theorem halfline_contour_shift_signed (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| < Real.pi/8) :
    (∫ x : ℝ in Ioi 0, saddleWeight t z (x : ℂ))=
      (∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I))+
        Complex.I*(∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)) := by
  have h0 : IntegrableOn (fun x : ℝ => saddleWeight t z (x : ℂ)) (Ioi 0) := by
    simpa using shifted_weight_integrable t z 0 (by simpa only [abs_zero] using (by positivity : (0 : ℝ)<Real.pi/8))
  have ha := intervalIntegral_tendsto_integral_Ioi 0 h0 tendsto_id
  have hb := intervalIntegral_tendsto_integral_Ioi 0 (shifted_weight_integrable t z h hh) tendsto_id
  have hr := (right_segment_tendsto_zero t z h hh).const_mul Complex.I
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

theorem vertical_pair_cancel (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| < Real.pi/8) :
    (∫ y : ℝ in 0..(-h), saddleWeight t (-z) ((y : ℂ)*Complex.I))=
      -(∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)) := by
  rw [intervalIntegral.integral_symm]
  have hc := intervalIntegral.integral_comp_neg (a := 0) (b := h)
    (fun y : ℝ => saddleWeight t (-z) ((y : ℂ)*Complex.I))
  simp only [neg_zero] at hc
  rw [← hc]
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  have hyabs := (vertical_abs_le h y hy).trans_lt hh
  have hw : (y : ℂ)*Complex.I ∈ strip := by
    change -Real.pi/8 < ((y : ℂ)*Complex.I).im ∧ ((y : ℂ)*Complex.I).im < Real.pi/8
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,Complex.ofReal_im,Complex.I_re,mul_zero,add_zero]
    constructor <;> linarith [(abs_lt.mp hyabs).1,(abs_lt.mp hyabs).2]
  have he : ((-y : ℝ) : ℂ)*Complex.I= -((y : ℂ)*Complex.I) := by push_cast; ring
  change saddleWeight t (-z) (((-y : ℝ) : ℂ)*Complex.I)=saddleWeight t z ((y : ℂ)*Complex.I)
  rw [he]
  exact weight_neg_neg t z _ hw

theorem flow_eq_paired_horizontal (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| < Real.pi/8) :
    RiemannQuarticFlow.flow t z=
      ((∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I))+
        (∫ x : ℝ in Ioi 0, saddleWeight t (-z) ((x : ℂ)-(h : ℂ)*Complex.I)))/2 := by
  rw [RiemannQuarticFlow.flow,RiemannQuarticPairedSaddle.jet_zero_eq_halfline,
    RiemannQuarticPairedSaddle.jet_zero_eq_halfline,
    halfline_contour_shift_signed t z h hh,halfline_contour_shift_signed t (-z) (-h) (by simpa using hh),
    vertical_pair_cancel t z h hh]
  simp only [Complex.ofReal_neg,neg_mul,← sub_eq_add_neg]
  ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticNaturalContour
