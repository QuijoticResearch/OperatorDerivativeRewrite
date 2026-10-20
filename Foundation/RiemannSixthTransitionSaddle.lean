import Foundation.RiemannEvenModelPhase
import Foundation.RiemannQuarticTransitionSaddle
/-! Degree-correct sixth-order model saddles in the bounded transition region.
Actual logarithmic correction and integrated zero control remain separate. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionSaddle
open RiemannEvenModelPhase RiemannEvenRealSaddle RiemannEvenSaddleBranch
open RiemannQuarticQuantitativeSaddle
open RiemannQuarticTransitionSaddle (realScale realScale_pos movingAnchor
  anchor_exponential anchor_displacement anchor_imaginary_bound)

theorem anchor_residual_identity (m : ℕ) (t u : ℝ) (z : ℂ)
    (hB : 2 ≤ realScale u) (hy : z.im ≤ 1) :
    modelDerivative m t (movingAnchor u z)+Complex.I*z=
      ((2*m : ℕ) : ℂ)*(t : ℂ)*((movingAnchor u z)^(2*m-1)-(u : ℂ)^(2*m-1))+
        modelDerivative m t (u : ℂ) := by
  have h := anchor_exponential u z hB hy
  have hreal : 4*(Real.pi : ℂ)*Complex.exp (4*(u : ℂ))=(realScale u : ℂ) := by
    simp only [realScale,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_exp]
  unfold modelDerivative
  rw [h,hreal]
  ring

theorem real_saddle_scale_lower (t u : ℝ) (hu : 1 ≤ u) (hs : phaseSlope 3 t u=0) :
    6*t*u^5+8 ≤ realScale u := by
  have h := (stationary_scale_bounds 3 t u hu hs).2
  norm_num at h
  dsimp [realScale]
  linarith

theorem anchor_residual_bound (t u L : ℝ) (z b : ℂ)
    (ht : 0 ≤ t) (hu : 1 ≤ u) (hL : 0 ≤ L)
    (hs : phaseSlope 3 t u=0) (hb : ‖b-(u : ℂ)‖ ≤ L) (hbn : ‖b‖ ≤ 2*u)
    (he : 4*(Real.pi : ℂ)*Complex.exp (4*b)=(realScale u : ℂ)+Complex.I*z) :
    ‖modelDerivative 3 t b+Complex.I*z‖ ≤ 186*L*t*u^4+1 := by
  have hid : modelDerivative 3 t b+Complex.I*z=
      6*(t : ℂ)*(b-(u : ℂ))*(b^4+b^3*(u : ℂ)+b^2*(u : ℂ)^2+b*(u : ℂ)^3+(u : ℂ)^4)+
        modelDerivative 3 t (u : ℂ) := by
    have hreal : 4*(Real.pi : ℂ)*Complex.exp (4*(u : ℂ))=(realScale u : ℂ) := by
      simp only [realScale,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_exp]
    unfold modelDerivative
    rw [he,hreal]
    ring
  have hsum : ‖b^4+b^3*(u : ℂ)+b^2*(u : ℂ)^2+b*(u : ℂ)^3+(u : ℂ)^4‖ ≤ 31*u^4 := by
    have h1 := norm_add_le (b^4) (b^3*(u : ℂ))
    have h2 := norm_add_le (b^4+b^3*(u : ℂ)) (b^2*(u : ℂ)^2)
    have h3 := norm_add_le (b^4+b^3*(u : ℂ)+b^2*(u : ℂ)^2) (b*(u : ℂ)^3)
    have h4 := norm_add_le (b^4+b^3*(u : ℂ)+b^2*(u : ℂ)^2+b*(u : ℂ)^3) ((u : ℂ)^4)
    simp only [norm_pow,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ u)] at h1 h2 h3 h4
    have hp4 := pow_le_pow_left₀ (norm_nonneg b) hbn 4
    have hp3 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg b) hbn 3)
      (by linarith : 0 ≤ u)
    have hp2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg b) hbn 2) (sq_nonneg u)
    have hp1 := mul_le_mul_of_nonneg_right hbn (pow_nonneg (by linarith : 0 ≤ u) 3)
    nlinarith
  rw [hid]
  calc
    _ ≤ ‖6*(t : ℂ)*(b-(u : ℂ))*(b^4+b^3*(u : ℂ)+b^2*(u : ℂ)^2+b*(u : ℂ)^3+(u : ℂ)^4)‖+
        ‖modelDerivative 3 t (u : ℂ)‖ := norm_add_le _ _
    _ ≤ (6*t)*L*(31*u^4)+1 := by
      simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]
      gcongr
      exact real_stationary_model_residual 3 t u hu hs
    _ = _ := by ring

theorem model_saddle_near_moving_anchor (t u L : ℝ) (z b : ℂ)
    (ht : 1 ≤ t) (hL : 0 ≤ L) (hu : 65536*(L+1) ≤ u)
    (hs : phaseSlope 3 t u=0) (hy : z.im ≤ 1) (hb : ‖b-(u : ℂ)‖ ≤ L)
    (he : 4*(Real.pi : ℂ)*Complex.exp (4*b)=(realScale u : ℂ)+Complex.I*z) :
    ∃! w, w ∈ closedBall b (1/1024) ∧ modelDerivative 3 t w= -(Complex.I*z) := by
  have hu1 : 1 ≤ u := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hB := real_saddle_scale_lower t u hu1 hs
  have hQ : 1 ≤ t*u^4 := by
    have hp : 1 ≤ u^4 := one_le_pow₀ hu1
    nlinarith
  have hB8 : 8 ≤ realScale u := by
    have hp : 0 ≤ t*u^5 := by positivity
    linarith
  have hbn : ‖b‖ ≤ 2*u := by
    have hn := norm_add_le (b-(u : ℂ)) (u : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ u)] at hn
    linarith
  let A : ℂ := -4*((realScale u : ℂ)+Complex.I*z)
  have hA : 2*realScale u ≤ ‖A‖ := by
    have hr := Complex.re_le_norm ((realScale u : ℂ)+Complex.I*z)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_sub] at hr
    simp only [A, norm_mul, norm_neg, Complex.norm_ofNat]
    linarith
  have hAn : A ≠ 0 := norm_pos_iff.mp (by linarith)
  have hdiff : ∀ w ∈ closedBall b (1/1024), DifferentiableAt ℂ (modelDerivative 3 t) w :=
    fun w _ => (modelDerivative_hasDerivAt 3 t w).differentiableAt
  have hbound : ∀ w ∈ closedBall b (1/1024), ‖deriv (modelDerivative 3 t) w-A‖ ≤ ‖A‖/2 := by
    intro w hw
    have hd : ‖w-b‖ ≤ (1/1024 : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hwU : ‖w‖ ≤ 2*u := by
      have hwB := norm_add_le (w-b) b
      have hbU := norm_add_le (b-(u : ℂ)) (u : ℂ)
      rw [sub_add_cancel] at hwB
      rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ u)] at hbU
      linarith
    have hex := Complex.norm_exp_sub_one_le (x := 4*(w-b)) (by
      rw [norm_mul, Complex.norm_ofNat]
      linarith : ‖4*(w-b)‖ ≤ 1)
    have hexp : ‖Complex.exp (4*(w-b))-1‖ ≤ (1/128 : ℝ) := by
      rw [norm_mul, Complex.norm_ofNat] at hex
      linarith
    have heW : Complex.exp (4*w)=Complex.exp (4*b)*Complex.exp (4*(w-b)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have hid : deriv (modelDerivative 3 t) w-A=
        30*(t : ℂ)*w^4+A*(Complex.exp (4*(w-b))-1) := by
      rw [(modelDerivative_hasDerivAt 3 t w).deriv, heW]
      have h16 : 16*(Real.pi : ℂ)*Complex.exp (4*b)= -A := by
        dsimp [A]
        linear_combination 4*he
      dsimp [A] at *
      linear_combination -(Complex.exp (4*(w-b)))*h16
    have hpoly : 480*t*u^4 ≤ ‖A‖/4 := by
      have hp := mul_nonneg (show 0 ≤ 3*u-480 by linarith) (show 0 ≤ t*u^4 by positivity)
      nlinarith
    rw [hid]
    have hn := norm_add_le (30*(t : ℂ)*w^4) (A*(Complex.exp (4*(w-b))-1))
    simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0] at hn
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hwU 4)
      (show 0 ≤ 30*t by positivity)
    have hm := mul_le_mul_of_nonneg_left hexp (norm_nonneg A)
    nlinarith
  have hres := anchor_residual_bound t u L z b ht0 hu1 hL hs hb hbn he
  have hsmall : 186*L*t*u^4+1 ≤ ‖A‖/2048 := by
    have hp := mul_nonneg (show 0 ≤ 12*u-380928*L-2048 by linarith)
      (show 0 ≤ t*u^4 by positivity)
    nlinarith
  have htarget : -(Complex.I*z) ∈ closedBall (modelDerivative 3 t b) (‖A‖*(1/1024)/2) := by
    rw [mem_closedBall, dist_eq_norm]
    have hid : -(Complex.I*z)-modelDerivative 3 t b= -(modelDerivative 3 t b+Complex.I*z) := by ring
    rw [hid, norm_neg]
    linarith
  obtain ⟨w,hw,hr⟩ := scalar_ball_surj (modelDerivative 3 t) b A (1/1024)
    (by norm_num) hAn hdiff hbound htarget
  refine ⟨w, ⟨hw,hr⟩, ?_⟩
  intro v hv
  exact scalar_ball_injective (modelDerivative 3 t) b A (1/1024) hAn hdiff hbound hv.1 hw
    (hv.2.trans hr.symm)

theorem existsUnique_transition_model_saddle (t u M : ℝ) (z : ℂ)
    (ht : 1 ≤ t) (hM : 0 ≤ M) (hu : 65536*(M+7) ≤ u)
    (hs : phaseSlope 3 t u=0) (hy : z.im ≤ 1) (hz : ‖z‖ ≤ M*realScale u) :
    ∃! w, w ∈ closedBall (movingAnchor u z) (1/1024) ∧
      modelDerivative 3 t w= -(Complex.I*z) := by
  have hu1 : 1 ≤ u := by linarith
  have hB : 2 ≤ realScale u := by
    have hp : 0 ≤ t*u^5 := by positivity
    linarith [real_saddle_scale_lower t u hu1 hs]
  exact model_saddle_near_moving_anchor t u (M+6) z (movingAnchor u z) ht
    (by linarith) (by linarith) hs hy (anchor_displacement u M z hB hy hM hz)
    (anchor_exponential u z hB hy)

theorem transition_model_geometry (t u M : ℝ) (z w : ℂ)
    (ht : 1 ≤ t) (hM : 0 ≤ M) (hu : 65536*(M+7) ≤ u)
    (hs : phaseSlope 3 t u=0) (hy : z.im ≤ 1) (hz : ‖z‖ ≤ M*realScale u)
    (hw : w ∈ closedBall (movingAnchor u z) (1/1024))
    (hr : modelDerivative 3 t w= -(Complex.I*z)) :
    ‖w-(u : ℂ)‖ ≤ M+7 ∧ 64 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
      t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re ∧
      1 ≤ (Complex.exp (4*w)).re ∧ RiemannThetaComplexKernel.kernelComplex w ≠ 0 := by
  have hu1 : 1 ≤ u := by linarith
  have hB : 2 ≤ realScale u := by
    have hp : 0 ≤ t*u^5 := by positivity
    linarith [real_saddle_scale_lower t u hu1 hs]
  have hd : ‖w-movingAnchor u z‖ ≤ (1/1024 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hw
  have hdu := anchor_displacement u M z hB hy hM hz
  have hdU : ‖w-(u : ℂ)‖ ≤ M+7 := by
    have hn := norm_add_le (w-movingAnchor u z) (movingAnchor u z-(u : ℂ))
    rw [sub_add_sub_cancel] at hn
    linarith
  have hre := Complex.abs_re_le_norm (w-(u : ℂ))
  simp only [Complex.sub_re,Complex.ofReal_re] at hre
  have hwre : 64 ≤ w.re := by linarith [(abs_le.mp (hre.trans hdU)).1]
  have hwi := Complex.abs_im_le_norm (w-movingAnchor u z)
  simp only [Complex.sub_im] at hwi
  have hwim : |w.im| ≤ 1/2 := by
    have hh := abs_add_le (w.im-(movingAnchor u z).im) (movingAnchor u z).im
    rw [sub_add_cancel] at hh
    linarith [anchor_imaginary_bound u z hB hy,Real.pi_lt_d2]
  have hw5 : (w^5).re=w.re^5-10*w.re^3*w.im^2+5*w.re*w.im^4 := by
    simp [pow_succ,Complex.mul_re,Complex.mul_im]
    <;> ring_nf <;> simp
  have hroot := congrArg Complex.re hr
  norm_num [modelDerivative,Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.mul_im] at hroot
  rw [hw5] at hroot
  have hwi2 : w.im^2 ≤ 1/4 := by nlinarith [(abs_le.mp hwim).1,(abs_le.mp hwim).2]
  have hc : 0 ≤ 5*w.re^2-60*w.im^2 := by nlinarith [sq_nonneg (w.re-64)]
  have hp := mul_nonneg (by positivity : 0 ≤ t*w.re^3) hc
  have hq : 0 ≤ 30*t*w.re*w.im^4 := by positivity
  have hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re := by nlinarith
  have hpow : 32 ≤ w.re^5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 2 ≤ w.re) 5
    norm_num at h
    exact h
  have ht5 : w.re^5 ≤ t*w.re^5 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 5]
  have hE1 : 1 ≤ (Complex.exp (4*w)).re := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4*Real.pi)).mp
    nlinarith [Real.pi_lt_four]
  exact ⟨hdU,hwre,hwim,hmargin,hE1,
    RiemannThetaComplexKernel.kernel_ne_zero w (by linarith) hE1⟩

theorem eventually_all_maxima_transition_model_saddle (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (RiemannEvenDomain.weighted 3 0 t 0) (Ici 0) u →
      ∀ z : ℂ, z.im ≤ 1 → ‖z‖ ≤ M*realScale u →
        ∃! w, w ∈ closedBall (movingAnchor u z) (1/1024) ∧
          modelDerivative 3 t w= -(Complex.I*z) := by
  filter_upwards [RiemannEvenRealSaddle.maxima_escape 3 (by norm_num)
    (65536*(M+7)) (by positivity),eventually_ge_atTop (1 : ℝ)] with t hU ht
  intro u hu hm z hy hz
  have huU := (hU u hu hm).le
  have hu0 : 0 < u := by linarith
  have hs := RiemannEvenRealSaddle.max_real_stationary 3 t u hu0 hm
  exact existsUnique_transition_model_saddle t u M z ht hM huU hs hy hz

theorem eventually_exists_transition_family (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, 65536*(M+7) ≤ u ∧ phaseSlope 3 t u=0 ∧
      ∀ z : ℂ, z.im ≤ 1 → ‖z‖ ≤ M*realScale u →
        ∃! w, w ∈ closedBall (movingAnchor u z) (1/1024) ∧
          modelDerivative 3 t w= -(Complex.I*z) := by
  filter_upwards [RiemannEvenRealSaddle.maxima_escape 3 (by norm_num)
    (65536*(M+7)) (by positivity),eventually_all_maxima_transition_model_saddle M hM]
    with t hU hmodels
  obtain ⟨u,hu,hm⟩ := RiemannEvenRealSaddle.exists_global_max 3 t
  have huU := (hU u hu hm).le
  have hu0 : 0 < u := by linarith
  have hs := RiemannEvenRealSaddle.max_real_stationary 3 t u hu0 hm
  exact ⟨u,huU,hs,hmodels u hu hm⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionSaddle
