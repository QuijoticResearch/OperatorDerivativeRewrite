import Foundation.RiemannEvenFarModelSaddle
import Foundation.RiemannSixthFarCorrection

/-! Constructed genuine arithmetic sixth-order far saddles at every
sufficiently large real frequency scale, for each fixed time. -/
noncomputable section
open Filter Set Metric Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarConstruction
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannThetaComplexKernel

theorem actual_weight_critical (t : ℝ) (z v : ℂ)
    (hv : 0 < (Complex.exp (4*v)).re) (hk : kernelComplex v ≠ 0)
    (hs : complexSlope 3 t v = -(Complex.I*z)) :
    HasDerivAt (fun w : ℂ => Complex.exp ((t : ℂ)*w^6+Complex.I*z*w)*kernelComplex w) 0 v ∧
      Complex.exp ((t : ℂ)*v^6+Complex.I*z*v)*kernelComplex v ≠ 0 := by
  have hkernel := kernelComplex_hasDerivAt v hv
  have he : (6*(t : ℂ)*v^5+Complex.I*z)*kernelComplex v+kernelDerivative v = 0 := by
    unfold complexSlope at hs
    rw [hkernel.deriv] at hs
    norm_num at hs
    field_simp [hk] at hs
    linear_combination hs
  have hp := ((((hasDerivAt_id v).pow 6).const_mul (t : ℂ)).add
    ((hasDerivAt_id v).const_mul (Complex.I*z))).cexp
  have hd : HasDerivAt (fun w : ℂ => Complex.exp ((t : ℂ)*w^6+Complex.I*z*w)*kernelComplex w)
      (Complex.exp ((t : ℂ)*v^6+Complex.I*z*v)*
        ((6*(t : ℂ)*v^5+Complex.I*z)*kernelComplex v+kernelDerivative v)) v := by
    convert hp.mul hkernel using 1
    · funext w; rfl
    · simp only [id_eq,Pi.add_apply,Pi.pow_apply]
      ring
  rw [he,mul_zero] at hd
  exact ⟨hd,mul_ne_zero (Complex.exp_ne_zero _) hk⟩

theorem sufficiently_large_scale (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ a : ℝ in atTop, 490000*(t+1)*(a+4)^5 ≤ 4*Real.pi*Real.exp (4*a) := by
  let C : ℝ := 490000*(t+1)*32
  have h := ((isLittleO_pow_exp_pos_mul_atTop 5 (b := 4) (by norm_num)).const_mul_left C).bound
    (show 0 < 4*Real.pi by positivity)
  filter_upwards [h,eventually_ge_atTop (4 : ℝ)] with a hb ha
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hb
  have hp : (a+4)^5 ≤ 32*a^5 := by
    have hpoly := pow_le_pow_left₀ (by linarith : 0 ≤ a+4) (by linarith : a+4 ≤ 2*a) 5
    simpa only [mul_pow,show (2 : ℝ)^5 = 32 by norm_num] using hpoly
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 490000*(t+1) by positivity)
  have hc : C*a^5 ≤ 4*Real.pi*Real.exp (4*a) := (le_abs_self _).trans hb
  exact hm.trans (by convert hc using 1 <;> dsimp [C] <;> ring)

theorem constructed_actual_far_saddles (t a : ℝ) (ht : 1 ≤ t) (ha : 120021 ≤ a)
    (hscale : 490000*(t+1)*(a+4)^5 ≤ 4*Real.pi*Real.exp (4*a)) :
    let x : ℝ := 4*Real.pi*Real.exp (4*a)
    ∃ w v : ℂ, w ∈ closedBall (RiemannQuarticFarModelSaddle.anchor a) (1/1024) ∧
      modelDerivative 3 t w = -(Complex.I*(x : ℂ)) ∧
      v ∈ closedBall w (1/x) ∧ complexSlope 3 t v = -(Complex.I*(x : ℂ)) ∧
      0 < (Complex.exp (4*v)).re ∧ kernelComplex v ≠ 0 := by
  let x : ℝ := 4*Real.pi*Real.exp (4*a)
  have hx0 : 0 < x := by dsimp [x]; positivity
  have ht0 : 0 ≤ t := by linarith
  have hb := RiemannQuarticFarModelSaddle.anchor_norm a (by linarith)
  have hsc : 10000*((((2*3 : ℕ) : ℝ)+1)^2)*(t+1)*(a+4)^(2*3-1) ≤ ‖(x : ℂ)‖ := by
    norm_num
    rw [abs_of_pos hx0]
    exact hscale
  obtain ⟨w,⟨hw,hroot⟩,_⟩ := RiemannEvenFarModelSaddle.anchored_complex_saddle 3 (by norm_num)
    t (a+4) (x : ℂ) ht0 (by linarith) hsc _ (by linarith) (RiemannQuarticFarModelSaddle.anchor_spec a)
  have hd : ‖w-RiemannQuarticFarModelSaddle.anchor a‖ ≤ (1/1024 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hw
  have hreal := (Complex.abs_re_le_norm (w-RiemannQuarticFarModelSaddle.anchor a)).trans hd
  have him := (Complex.abs_im_le_norm (w-RiemannQuarticFarModelSaddle.anchor a)).trans hd
  have hanchor_re : (RiemannQuarticFarModelSaddle.anchor a).re = a := by
    simp [RiemannQuarticFarModelSaddle.anchor,Complex.mul_re]
  have hanchor_im : (RiemannQuarticFarModelSaddle.anchor a).im = Real.pi/8 := by
    simp [RiemannQuarticFarModelSaddle.anchor,Complex.mul_im]
  simp only [Complex.sub_re,hanchor_re] at hreal
  simp only [Complex.sub_im,hanchor_im] at him
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hreal).1]
  have hi : |w.im| ≤ 1/2 := by
    have hh := abs_add_le (w.im-Real.pi/8) (Real.pi/8)
    rw [sub_add_cancel,abs_of_pos (by positivity : 0 < Real.pi/8)] at hh
    linarith [Real.pi_lt_d2]
  have hnorm : ‖w‖+1 ≤ a+4 := by
    have hh := norm_add_le (w-RiemannQuarticFarModelSaddle.anchor a) (RiemannQuarticFarModelSaddle.anchor a)
    rw [sub_add_cancel] at hh
    linarith
  have hp : 10000*(t*(‖w‖+1)^5+1) ≤ x := by
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖+1) hnorm 5
    have hm := mul_le_mul_of_nonneg_left hpow ht0
    have h1 : 1 ≤ (a+4)^5 := one_le_pow₀ (by linarith : 1 ≤ a+4)
    change 490000*(t+1)*(a+4)^5 ≤ x at hscale
    nlinarith
  have hx : 10000 ≤ x := by
    have hh : 0 ≤ t*(‖w‖+1)^5 := by positivity
    nlinarith
  obtain ⟨v,⟨hv,hactual⟩,_⟩ := RiemannSixthFarCorrection.actual_far_saddle t x ht hx w hr hi hp hroot
  have hdist : ‖v-w‖ ≤ 2/x := by
    have hh : ‖v-w‖ ≤ 1/x := by simpa only [mem_closedBall,dist_eq_norm] using hv
    have hfrac : 1/x ≤ 2/x := (div_le_div_iff_of_pos_right hx0).mpr (by norm_num)
    exact hh.trans hfrac
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hpol : 6*t*‖w‖^5+9 ≤ x := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 5]
  have hdom := RiemannSixthFarCorrection.neighbor_domain t x ht (by linarith) w v (by linarith) hi hroot hpol hdist
  exact ⟨w,v,hw,hroot,hv,hactual,by linarith [hdom.2.1],
    RiemannThetaComplexKernel.kernel_ne_zero v hdom.1 hdom.2.1⟩

theorem eventually_actual_far_saddles (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ a : ℝ in atTop,
      let x : ℝ := 4*Real.pi*Real.exp (4*a)
      ∃ w v : ℂ, w ∈ closedBall (RiemannQuarticFarModelSaddle.anchor a) (1/1024) ∧
        modelDerivative 3 t w = -(Complex.I*(x : ℂ)) ∧
        v ∈ closedBall w (1/x) ∧ complexSlope 3 t v = -(Complex.I*(x : ℂ)) ∧
        HasDerivAt (fun q : ℂ => Complex.exp ((t : ℂ)*q^6+Complex.I*(x : ℂ)*q)*kernelComplex q) 0 v ∧
        Complex.exp ((t : ℂ)*v^6+Complex.I*(x : ℂ)*v)*kernelComplex v ≠ 0 := by
  filter_upwards [sufficiently_large_scale t ht,eventually_ge_atTop (120021 : ℝ)] with a hs ha
  obtain ⟨w,v,hw,hmodel,hv,hactual,hdom,hkernel⟩ := constructed_actual_far_saddles t a ht ha hs
  have hcrit := actual_weight_critical t ((4*Real.pi*Real.exp (4*a) : ℝ) : ℂ) v hdom hkernel hactual
  exact ⟨w,v,hw,hmodel,hv,hactual,hcrit⟩

theorem eventually_frequency_actual_saddles (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ x : ℝ in atTop, ∃ v : ℂ, complexSlope 3 t v = -(Complex.I*(x : ℂ)) ∧
      HasDerivAt (fun q : ℂ => Complex.exp ((t : ℂ)*q^6+Complex.I*(x : ℂ)*q)*kernelComplex q) 0 v ∧
      Complex.exp ((t : ℂ)*v^6+Complex.I*(x : ℂ)*v)*kernelComplex v ≠ 0 := by
  have hlin : Tendsto (fun x : ℝ => x/(4*Real.pi)) atTop atTop := tendsto_id.atTop_div_const (by positivity)
  have hlim := (Real.tendsto_log_atTop.comp hlin).atTop_div_const (by norm_num : (0 : ℝ) < 4)
  filter_upwards [hlim.eventually (eventually_actual_far_saddles t ht),eventually_gt_atTop (0 : ℝ)] with x hex hx
  obtain ⟨w,v,hw,hmodel,hv,hactual,hcrit,hne⟩ := hex
  have hid : 4*Real.pi*Real.exp (4*(Real.log (x/(4*Real.pi))/4)) = x := by
    rw [show 4*(Real.log (x/(4*Real.pi))/4) = Real.log (x/(4*Real.pi)) by ring,
      Real.exp_log (by positivity : (0 : ℝ) < x/(4*Real.pi))]
    field_simp
  simp only [Function.comp_def] at hactual hcrit hne
  rw [hid] at hactual hcrit hne
  exact ⟨v,hactual,hcrit,hne⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarConstruction
