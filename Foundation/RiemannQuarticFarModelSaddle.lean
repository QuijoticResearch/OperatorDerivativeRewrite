import Foundation.RiemannQuarticNaturalContour
/-! Constructed high-frequency leading-model saddles and actual arithmetic links.
Uniqueness is local to the stated anchor ball. For each fixed t>=1 all
sufficiently large real frequencies are covered. Actual phase slope residual
is bounded but is not set to zero; full saddle correction/dominance is open. -/
noncomputable section
open Set Metric Complex Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarModelSaddle
open RiemannQuarticSaddleTheta RiemannQuarticQuantitativeSaddle

theorem modelDerivative_hasDerivAt (t : ℝ) (w : ℂ) :
    HasDerivAt (modelDerivative t) (12*(t : ℂ)*w^2-16*(Real.pi : ℂ)*Complex.exp (4*w)) w := by
  have h := (((((hasDerivAt_id w).pow 3).const_mul (4*(t : ℂ))).add_const 9).sub
    ((((hasDerivAt_id w).const_mul (4 : ℂ)).cexp).const_mul (4*(Real.pi : ℂ))))
  convert h using 1
  · funext v
    rfl
  · simp only [id_eq]
    ring

theorem anchored_far_saddle (t x M : ℝ) (ht : 0 ≤ t) (hM : 1 ≤ M)
    (hx : 10000*(t+1)*M^3 ≤ x) (b : ℂ) (hb : ‖b‖ ≤ M-1)
    (hanchor : 4*(Real.pi : ℂ)*Complex.exp (4*b)=Complex.I*(x : ℂ)) :
    ∃! w, w ∈ closedBall b (1/1024) ∧ modelDerivative t w= -(Complex.I*(x : ℂ)) := by
  have hM0 : 0 ≤ M := by linarith
  have hM3 : 1 ≤ M^3 := one_le_pow₀ hM
  have hM23 : M^2 ≤ M^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sq_nonneg M)]
  have htm : 0 ≤ t*M^3 := by positivity
  have hx0 : 0 < x := by nlinarith
  have hpoly : 12*t*M^2 ≤ x := by
    have h := mul_le_mul_of_nonneg_left hM23 ht
    nlinarith
  have hres : 4*t*M^3+9 ≤ x/512 := by nlinarith
  let A := -(4 : ℂ)*Complex.I*(x : ℂ)
  have hA : ‖A‖=4*x := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0,mul_one]
  have hAn : A ≠ 0 := norm_pos_iff.mp (by rw [hA]; positivity)
  have hdiff : ∀ w ∈ closedBall b (1/1024), DifferentiableAt ℂ (modelDerivative t) w :=
    fun w _ => (modelDerivative_hasDerivAt t w).differentiableAt
  have hbound : ∀ w ∈ closedBall b (1/1024), ‖deriv (modelDerivative t) w-A‖ ≤ ‖A‖/2 := by
    intro w hw
    have hd : ‖w-b‖ ≤ (1/1024 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have hnorm : ‖w‖ ≤ M := by
      have h := norm_add_le (w-b) b
      simp only [sub_add_cancel] at h
      linarith
    have he := Complex.norm_exp_sub_one_le (x := 4*(w-b)) (by
      rw [norm_mul,Complex.norm_ofNat]
      linarith : ‖4*(w-b)‖ ≤ 1)
    have hexp : ‖Complex.exp (4*(w-b))-1‖ ≤ (1/128 : ℝ) := by
      rw [norm_mul,Complex.norm_ofNat] at he
      linarith
    have heW : Complex.exp (4*w)=Complex.exp (4*b)*Complex.exp (4*(w-b)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have h16 : 16*(Real.pi : ℂ)*Complex.exp (4*w)=
        (4*Complex.I*(x : ℂ))*Complex.exp (4*(w-b)) := by
      calc
        _ = 4*(4*(Real.pi : ℂ)*Complex.exp (4*b))*Complex.exp (4*(w-b)) := by rw [heW]; ring
        _ = _ := by rw [hanchor]; ring
    have hid : deriv (modelDerivative t) w-A=
        12*(t : ℂ)*w^2-(4*Complex.I*(x : ℂ))*(Complex.exp (4*(w-b))-1) := by
      rw [(modelDerivative_hasDerivAt t w).deriv,h16]
      dsimp [A]
      ring
    rw [hid,hA]
    have hn := norm_sub_le (12*(t : ℂ)*w^2) ((4*Complex.I*(x : ℂ))*(Complex.exp (4*(w-b))-1))
    simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg ht,abs_of_pos hx0,Complex.norm_I,mul_one] at hn
    have hp := pow_le_pow_left₀ (norm_nonneg w) hnorm 2
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 12*t)
    have hg := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 4*x)
    nlinarith
  have hc : modelDerivative t b=4*(t : ℂ)*b^3+9-Complex.I*(x : ℂ) := by
    unfold modelDerivative
    rw [hanchor]
  have htarget : -(Complex.I*(x : ℂ)) ∈ closedBall (modelDerivative t b) (‖A‖*(1/1024)/2) := by
    rw [mem_closedBall,dist_eq_norm,hc,hA]
    have he : -(Complex.I*(x : ℂ))-(4*(t : ℂ)*b^3+9-Complex.I*(x : ℂ))= -(4*(t : ℂ)*b^3+9) := by ring
    rw [he,norm_neg]
    have hn := norm_add_le (4*(t : ℂ)*b^3) (9 : ℂ)
    simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht] at hn
    have hp := pow_le_pow_left₀ (norm_nonneg b) (le_trans hb (by linarith : M-1 ≤ M)) 3
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4*t)
    nlinarith
  obtain ⟨w,hw,hroot⟩ := scalar_ball_surj (modelDerivative t) b A (1/1024) (by norm_num) hAn hdiff hbound htarget
  refine ⟨w,⟨hw,hroot⟩,?_⟩
  intro v hv
  exact scalar_ball_injective (modelDerivative t) b A (1/1024) hAn hdiff hbound hv.1 hw (hv.2.trans hroot.symm)

def anchor (a : ℝ) : ℂ := (a : ℂ)+((Real.pi/8 : ℝ) : ℂ)*Complex.I

theorem anchor_spec (a : ℝ) :
    4*(Real.pi : ℂ)*Complex.exp (4*anchor a)=Complex.I*((4*Real.pi*Real.exp (4*a) : ℝ) : ℂ) := by
  have he : 4*anchor a=((4*a : ℝ) : ℂ)+((Real.pi/2 : ℝ) : ℂ)*Complex.I := by dsimp [anchor]; push_cast; ring
  rw [he,Complex.exp_add]
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.exp_pi_div_two_mul_I]
  rw [← Complex.ofReal_exp]
  push_cast
  ring

theorem anchor_norm (a : ℝ) (ha : 0 ≤ a) : ‖anchor a‖ ≤ (a+2)-1 := by
  have h := Complex.norm_le_abs_re_add_abs_im (anchor a)
  simp only [anchor,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,
    sub_zero,add_zero,zero_add,abs_of_nonneg ha,abs_of_pos (by positivity : (0 : ℝ)<Real.pi/8)] at h
  change ‖anchor a‖ ≤ a+Real.pi/8 at h
  linarith [Real.pi_lt_four]

theorem concrete_far_saddle (t a : ℝ) (ht : 0 ≤ t) (ha : 4 ≤ a)
    (hscale : 10000*(t+1)*(a+2)^3 ≤ 4*Real.pi*Real.exp (4*a)) :
    ∃! w, w ∈ closedBall (anchor a) (1/1024) ∧
      modelDerivative t w= -(Complex.I*((4*Real.pi*Real.exp (4*a) : ℝ) : ℂ)) :=
  anchored_far_saddle t _ (a+2) ht (by linarith) hscale _ (anchor_norm a (by linarith)) (anchor_spec a)

theorem eventually_concrete_far_saddle (t : ℝ) (ht : 0 ≤ t) :
    ∀ᶠ a : ℝ in atTop, ∃! w, w ∈ closedBall (anchor a) (1/1024) ∧
      modelDerivative t w= -(Complex.I*((4*Real.pi*Real.exp (4*a) : ℝ) : ℂ)) := by
  filter_upwards [RiemannQuarticDomain.quartic_exponent_dominated (80000*(t+1)) 0,
    eventually_ge_atTop (4 : ℝ)] with a hdom ha
  apply concrete_far_saddle t a ht ha
  have ha0 : 0 ≤ a := by linarith
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ a+2) (by linarith : a+2 ≤ 2*a) 3
  have h34 : a^3 ≤ a^4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ a-1) (pow_nonneg ha0 3)]
  have hM : (a+2)^3 ≤ 8*a^4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 10000*(t+1))
  simp only [zero_mul,add_zero] at hdom
  nlinarith [Real.pi_pos,Real.exp_pos (4*a)]

theorem far_saddle_geometry (a : ℝ) (ha : 4 ≤ a) (w : ℂ)
    (hw : w ∈ closedBall (anchor a) (1/1024)) : 2 ≤ w.re ∧ |w.im| ≤ 1/2 := by
  have hd : ‖w-anchor a‖ ≤ (1/1024 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hr := (Complex.abs_re_le_norm (w-anchor a)).trans hd
  have hi := (Complex.abs_im_le_norm (w-anchor a)).trans hd
  have hbr : (anchor a).re=a := by simp [anchor]
  have hbi : (anchor a).im=Real.pi/8 := by simp [anchor]
  simp only [Complex.sub_re,Complex.sub_im,hbr,hbi] at hr hi
  constructor
  · linarith [(abs_le.mp hr).1]
  · apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hi).1,(abs_le.mp hi).2,Real.pi_lt_d2,Real.pi_pos]

theorem eventually_far_saddle_kernel_control (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ a : ℝ in atTop, ∃ w : ℂ, w ∈ closedBall (anchor a) (1/1024) ∧
      modelDerivative t w= -(Complex.I*((4*Real.pi*Real.exp (4*a) : ℝ) : ℂ)) ∧
      2 ≤ w.re ∧ |w.im| ≤ 1/2 ∧ RiemannThetaComplexKernel.kernelComplex w ≠ 0 ∧
      ∀ k : ℕ, k ≤ 4 → ‖complexThetaTail k 1 (Complex.exp (4*w))‖ ≤
        32*Real.exp (-(3/4 : ℝ)*(t*w.re^3+9))*‖complexThetaTerm k (Complex.exp (4*w)) 0‖ := by
  filter_upwards [eventually_concrete_far_saddle t (by linarith),eventually_ge_atTop (4 : ℝ)] with a hex ha
  obtain ⟨w,⟨hw,hs⟩,_⟩ := hex
  have hg := far_saddle_geometry a ha w hw
  have hu1 : 1 ≤ w.re := by linarith [hg.1]
  have hcub : 8 ≤ w.re^3 := by nlinarith [mul_nonneg (by linarith : 0 ≤ w.re-2) (sq_nonneg w.re)]
  have hts : 7 ≤ t*w.re^3 := by nlinarith
  have hn := RiemannThetaComplexKernel.kernel_ne_zero_at_model_saddle t (4*Real.pi*Real.exp (4*a)) w (by linarith) hu1 hg.2 hs hts
  refine ⟨w,hw,hs,hg.1,hg.2,hn,?_⟩
  intro k hk
  exact saddle_theta_relative t (4*Real.pi*Real.exp (4*a)) w (by linarith) hu1 hg.2 hs k hk


theorem model_saddle_in_strip (t x : ℝ) (ht : 0 ≤ t) (w : ℂ) (ha : 1 ≤ w.re)
    (hb : |w.im| ≤ 1/2) (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) :
    |w.im| < Real.pi/8 := by
  have hR := saddle_real_lower t x w ht ha hb hs
  have hpow : 0 ≤ t*w.re^3 := by positivity
  have hE : 0 < (Complex.exp (4*w)).re := by nlinarith [Real.pi_pos]
  have heq : (Complex.exp (4*w)).re=Real.exp (4*w.re)*Real.cos (4*w.im) := by simp [Complex.exp_re,Complex.mul_re,Complex.mul_im]
  rw [heq] at hE
  have hc : 0 < Real.cos (4*w.im) := (mul_pos_iff_of_pos_left (Real.exp_pos (4*w.re))).mp hE
  have him : |4*w.im| ≤ 2 := by rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<4)]; linarith
  have hlt : |4*w.im| < Real.pi/2 := by
    by_contra hn
    have hh := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt hn)
      (by linarith [Real.pi_gt_three] : |4*w.im| ≤ Real.pi+Real.pi/2)
    rw [Real.cos_abs] at hh
    linarith
  rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<4)] at hlt
  linarith

theorem eventually_frequency_model_control (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ x : ℝ in atTop, ∃ w : ℂ,
      w ∈ closedBall (anchor (Real.log (x/(4*Real.pi))/4)) (1/1024) ∧
      modelDerivative t w= -(Complex.I*(x : ℂ)) ∧
      2 ≤ w.re ∧ |w.im| < Real.pi/8 ∧ RiemannThetaComplexKernel.kernelComplex w ≠ 0 ∧
      ∀ k : ℕ, k ≤ 4 → ‖complexThetaTail k 1 (Complex.exp (4*w))‖ ≤
        32*Real.exp (-(3/4 : ℝ)*(t*w.re^3+9))*‖complexThetaTerm k (Complex.exp (4*w)) 0‖ := by
  have hlin : Tendsto (fun x : ℝ => x/(4*Real.pi)) atTop atTop := tendsto_id.atTop_div_const (by positivity)
  have hlog := Real.tendsto_log_atTop.comp hlin
  have hlim := hlog.atTop_div_const (by norm_num : (0 : ℝ)<4)
  filter_upwards [hlim.eventually (eventually_far_saddle_kernel_control t ht),eventually_gt_atTop (0 : ℝ)] with x hex hx
  obtain ⟨w,hw,hs,ha,hb,hn,htail⟩ := hex
  have hid : 4*Real.pi*Real.exp (4*(Real.log (x/(4*Real.pi))/4))=x := by
    rw [show 4*(Real.log (x/(4*Real.pi))/4)=Real.log (x/(4*Real.pi)) by ring,
      Real.exp_log (by positivity : (0 : ℝ)<x/(4*Real.pi))]
    field_simp
  simp only [Function.comp_def] at hs hw
  rw [hid] at hs
  exact ⟨w,hw,hs,ha,model_saddle_in_strip t x (by linarith) w (by linarith) hb hs,hn,htail⟩

theorem eventually_frequency_model_contour (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ x : ℝ in atTop, ∃ w : ℂ,
      modelDerivative t w= -(Complex.I*(x : ℂ)) ∧ 2 ≤ w.re ∧ |w.im| < Real.pi/8 ∧
      RiemannThetaComplexKernel.kernelComplex w ≠ 0 ∧
      RiemannQuarticFlow.flow t (x : ℂ)=
        ((∫ s : ℝ in Ioi 0, RiemannQuarticFrequencyBranch.saddleWeight t (x : ℂ) ((s : ℂ)+(w.im : ℂ)*Complex.I))+
          (∫ s : ℝ in Ioi 0, RiemannQuarticFrequencyBranch.saddleWeight t (-(x : ℂ)) ((s : ℂ)-(w.im : ℂ)*Complex.I)))/2 := by
  filter_upwards [eventually_frequency_model_control t ht] with x hex
  obtain ⟨w,hw,hs,ha,hb,hn,htail⟩ := hex
  exact ⟨w,hs,ha,hb,hn,RiemannQuarticNaturalContour.flow_eq_paired_horizontal t (x : ℂ) w.im hb⟩


theorem actual_slope_residual_at_model (t x : ℝ) (ht : 1 ≤ t) (w : ℂ)
    (ha : 2 ≤ w.re) (hb : |w.im| ≤ 1/2) (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) :
    ‖RiemannQuarticSaddleBranch.complexSlope t w+Complex.I*(x : ℂ)‖ ≤
      5*Real.exp (-4*w.re)+30000*Real.exp (4*w.re)*Real.exp (-(3/4 : ℝ)*(t*w.re^3+9)) := by
  have ht0 : 0 ≤ t := by linarith
  have hu1 : 1 ≤ w.re := by linarith
  have hcub : 8 ≤ w.re^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤2) ha 3
    norm_num at h
    exact h
  have hts : 7 ≤ t*w.re^3 := by nlinarith
  have hreal := saddle_real_lower t x w ht0 hu1 hb hs
  have hR : 1 ≤ (Complex.exp (4*w)).re := by
    have hlow : 16/(4*Real.pi) ≤ (Complex.exp (4*w)).re := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ)<4*Real.pi)).mpr
      nlinarith
    have h1 : (1 : ℝ) ≤ 16/(4*Real.pi) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ)<4*Real.pi)).mpr
      nlinarith [Real.pi_lt_four]
    exact h1.trans hlow
  have h := RiemannQuarticSaddleNeighborhood.logDerivative_coarse_bound w (by linarith) hR
  have heq : RiemannQuarticSaddleBranch.complexSlope t w-modelDerivative t w=
      RiemannThetaComplexKernel.kernelDerivative w/RiemannThetaComplexKernel.kernelComplex w-
        (9-4*(Real.pi : ℂ)*Complex.exp (4*w)) := by
    unfold RiemannQuarticSaddleBranch.complexSlope modelDerivative
    rw [(RiemannThetaComplexKernel.kernelComplex_hasDerivAt w (by linarith : 0 < (Complex.exp (4*w)).re)).deriv]
    ring
  have hid : RiemannQuarticSaddleBranch.complexSlope t w+Complex.I*(x : ℂ)=
      RiemannQuarticSaddleBranch.complexSlope t w-modelDerivative t w := by rw [hs]; ring
  rw [hid,heq]
  apply h.trans
  have hex : Real.exp (-3*Real.pi*(Complex.exp (4*w)).re) ≤
      Real.exp (-(3/4 : ℝ)*(t*w.re^3+9)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hex (by positivity : 0 ≤ 30000*Real.exp (4*w.re)))


theorem scalar_residual_envelope (t r : ℝ) (ht : 1 ≤ t) (hr : 4 ≤ r) :
    5*Real.exp (-4*r)+30000*Real.exp (4*r)*Real.exp (-(3/4 : ℝ)*(t*r^3+9)) ≤
      30005*Real.exp (-r) := by
  have hr0 : 0 ≤ r := by linarith
  have hr2 : 16 ≤ r^2 := by nlinarith
  have hr3 : 16*r ≤ r^3 := by
    have h := mul_le_mul_of_nonneg_right hr2 hr0
    nlinarith
  have htr : r^3 ≤ t*r^3 := by nlinarith [pow_nonneg hr0 3]
  have h1 : Real.exp (-4*r) ≤ Real.exp (-r) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (4*r)*Real.exp (-(3/4 : ℝ)*(t*r^3+9)) ≤ Real.exp (-r) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ = 5*Real.exp (-4*r)+30000*(Real.exp (4*r)*Real.exp (-(3/4 : ℝ)*(t*r^3+9))) := by ring
    _ ≤ 5*Real.exp (-r)+30000*Real.exp (-r) := add_le_add
      (mul_le_mul_of_nonneg_left h1 (by norm_num)) (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = _ := by ring

theorem residual_in_anchor_ball (t a x : ℝ) (ht : 1 ≤ t) (ha : 8 ≤ a) (w : ℂ)
    (hw : w ∈ closedBall (anchor a) (1/1024))
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) :
    ‖RiemannQuarticSaddleBranch.complexSlope t w+Complex.I*(x : ℂ)‖ ≤
      30005*Real.exp (-a/2) := by
  have hg := far_saddle_geometry a (by linarith) w hw
  have hd : ‖w-anchor a‖ ≤ (1/1024 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hr := (Complex.abs_re_le_norm (w-anchor a)).trans hd
  have hbr : (anchor a).re=a := by simp [anchor]
  simp only [Complex.sub_re,hbr] at hr
  have hrea : a/2 ≤ w.re := by linarith [(abs_le.mp hr).1]
  have hr4 : 4 ≤ w.re := by linarith
  have h := (actual_slope_residual_at_model t x ht w hg.1 hg.2 hs).trans
    (scalar_residual_envelope t w.re ht hr4)
  exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : -w.re ≤ -a/2)) (by norm_num))


end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarModelSaddle
