import Foundation.RiemannQuarticComplexModelSaddle
import Mathlib.Analysis.Real.Pi.Bounds
/-! Moving logarithmic anchors in the quartic transition region.
The real saddle scale is retained in the exponential anchor. These are
leading-model saddle constructions; actual saddle correction and uniform
integrated errors remain separate obligations. -/
noncomputable section
open Set Metric Complex Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionSaddle
open RiemannQuarticSaddleTheta RiemannQuarticFarModelSaddle
open RiemannQuarticQuantitativeSaddle RiemannQuarticSaddleBranch
open RiemannQuarticSaddleTimes

def realScale (u : ℝ) : ℝ := 4*Real.pi*Real.exp (4*u)

def movingAnchor (u : ℝ) (z : ℂ) : ℂ :=
  (u : ℂ)+Complex.log (1+Complex.I*z/(realScale u : ℂ))/4

theorem realScale_pos (u : ℝ) : 0 < realScale u := by
  unfold realScale
  positivity

theorem anchor_argument_re (u : ℝ) (z : ℂ) :
    (1+Complex.I*z/(realScale u : ℂ)).re=1-z.im/realScale u := by
  simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  field_simp [ne_of_gt (realScale_pos u)]
  ring

theorem anchor_argument_half_plane (u : ℝ) (z : ℂ)
    (hB : 2 ≤ realScale u) (hy : z.im ≤ 1) :
    (1/2 : ℝ) ≤ (1+Complex.I*z/(realScale u : ℂ)).re := by
  rw [anchor_argument_re]
  have h : z.im/realScale u ≤ 1/2 :=
    (div_le_iff₀ (realScale_pos u)).mpr (by linarith)
  linarith

theorem movingAnchor_analyticAt (u : ℝ) (z : ℂ)
    (hB : 2 ≤ realScale u) (hy : z.im ≤ 1) :
    AnalyticAt ℂ (movingAnchor u) z := by
  have hq : 1+Complex.I*z/(realScale u : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by
      linarith [anchor_argument_half_plane u z hB hy]))
  have ha : AnalyticAt ℂ (fun v : ℂ => 1+Complex.I*v/(realScale u : ℂ)) z := by fun_prop
  have hl := ha.clog hq
  exact analyticAt_const.add hl.div_const

theorem anchor_exponential (u : ℝ) (z : ℂ)
    (hB : 2 ≤ realScale u) (hy : z.im ≤ 1) :
    4*(Real.pi : ℂ)*Complex.exp (4*movingAnchor u z)=
      (realScale u : ℂ)+Complex.I*z := by
  have hq := anchor_argument_half_plane u z hB hy
  have hne : 1+Complex.I*z/(realScale u : ℂ) ≠ 0 := by
    intro h
    rw [h] at hq
    norm_num at hq
  have hfour : 4*movingAnchor u z=4*(u : ℂ)+Complex.log (1+Complex.I*z/(realScale u : ℂ)) := by
    unfold movingAnchor
    ring
  rw [hfour, Complex.exp_add, Complex.exp_log hne]
  have hreal : 4*(Real.pi : ℂ)*Complex.exp (4*(u : ℂ))=(realScale u : ℂ) := by
    simp only [realScale, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_exp]
  rw [← mul_assoc, hreal]
  field_simp [ne_of_gt (realScale_pos u)]

theorem anchor_residual_identity (t u : ℝ) (z : ℂ)
    (hB : 2 ≤ realScale u) (hy : z.im ≤ 1) :
    modelDerivative t (movingAnchor u z)+Complex.I*z=
      4*(t : ℂ)*((movingAnchor u z)^3-(u : ℂ)^3)+modelDerivative t (u : ℂ) := by
  have h := anchor_exponential u z hB hy
  have hreal : 4*(Real.pi : ℂ)*Complex.exp (4*(u : ℂ))=(realScale u : ℂ) := by
    simp only [realScale, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_exp]
  unfold modelDerivative
  rw [h, hreal]
  ring

theorem log_norm_half_plane (q : ℂ) (hq : (1/2 : ℝ) ≤ q.re) :
    ‖Complex.log q‖ ≤ ‖q‖+5 := by
  have hn : (1/2 : ℝ) ≤ ‖q‖ := hq.trans (Complex.re_le_norm q)
  have hp : 0 < ‖q‖ := by linarith
  have hinv : ‖q‖⁻¹ ≤ 2 := by
    have h : (1 : ℝ)/‖q‖ ≤ 2 := (div_le_iff₀ hp).mpr (by linarith)
    simpa using h
  have hlo := Real.one_sub_inv_le_log_of_pos hp
  have hhi := Real.log_le_sub_one_of_pos hp
  have hl : |Real.log ‖q‖| ≤ ‖q‖+1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h := Complex.norm_le_abs_re_add_abs_im (Complex.log q)
  rw [Complex.log_re, Complex.log_im] at h
  linarith [Complex.abs_arg_le_pi q, Real.pi_lt_four]

theorem anchor_displacement (u M : ℝ) (z : ℂ)
    (hB : 2 ≤ realScale u) (hy : z.im ≤ 1) (hM : 0 ≤ M)
    (hz : ‖z‖ ≤ M*realScale u) :
    ‖movingAnchor u z-(u : ℂ)‖ ≤ M+6 := by
  have hq : ‖1+Complex.I*z/(realScale u : ℂ)‖ ≤ 1+M := by
    have h := norm_add_le (1 : ℂ) (Complex.I*z/(realScale u : ℂ))
    simp only [norm_one, norm_div, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (realScale_pos u)] at h
    have hd := (div_le_iff₀ (realScale_pos u)).mpr hz
    linarith
  have hl := log_norm_half_plane _ (anchor_argument_half_plane u z hB hy)
  simp only [movingAnchor, add_sub_cancel_left, norm_div, Complex.norm_ofNat]
  linarith

theorem anchor_imaginary_bound (u : ℝ) (z : ℂ)
    (hB : 2 ≤ realScale u) (hy : z.im ≤ 1) :
    |(movingAnchor u z).im| ≤ Real.pi/8 := by
  have hr := anchor_argument_half_plane u z hB hy
  have ha := (Complex.abs_arg_le_pi_div_two_iff).mpr (by linarith :
    0 ≤ (1+Complex.I*z/(realScale u : ℂ)).re)
  have h := div_le_div_of_nonneg_right ha (by norm_num : (0 : ℝ) ≤ 4)
  have he : Real.pi/2/4=Real.pi/8 := by ring
  rw [he] at h
  simpa [movingAnchor, Complex.log_im, abs_div] using h

theorem real_saddle_model_residual (t u : ℝ) (hu : 1 ≤ u) (hs : phaseSlope t u=0) :
    ‖modelDerivative t (u : ℂ)‖ ≤ 1 := by
  have he := RiemannQuarticSaddleNeighborhood.slope_model_error_on_neighborhood
    t u hu (u : ℂ) (by simp)
  rw [complexSlope_real, hs, Complex.ofReal_zero, zero_sub, norm_neg] at he
  exact he

theorem real_saddle_scale_lower (t u : ℝ) (hu : 1 ≤ u) (hs : phaseSlope t u=0) :
    4*t*u^3+8 ≤ realScale u := by
  have h := (RiemannQuarticCurvature.stationary_scale_bounds t u hu hs).2
  unfold realScale
  linarith

theorem anchor_residual_bound (t u L : ℝ) (z b : ℂ)
    (ht : 0 ≤ t) (hu : 1 ≤ u) (hL : 0 ≤ L)
    (hs : phaseSlope t u=0) (hb : ‖b-(u : ℂ)‖ ≤ L) (hbn : ‖b‖ ≤ 2*u)
    (he : 4*(Real.pi : ℂ)*Complex.exp (4*b)=(realScale u : ℂ)+Complex.I*z) :
    ‖modelDerivative t b+Complex.I*z‖ ≤ 28*L*t*u^2+1 := by
  have hid : modelDerivative t b+Complex.I*z=
      4*(t : ℂ)*(b-(u : ℂ))*(b^2+b*(u : ℂ)+(u : ℂ)^2)+modelDerivative t (u : ℂ) := by
    have hreal : 4*(Real.pi : ℂ)*Complex.exp (4*(u : ℂ))=(realScale u : ℂ) := by
      simp only [realScale, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_exp]
    unfold modelDerivative
    rw [he, hreal]
    ring
  have hsum : ‖b^2+b*(u : ℂ)+(u : ℂ)^2‖ ≤ 7*u^2 := by
    have h1 := norm_add_le (b^2+b*(u : ℂ)) ((u : ℂ)^2)
    have h2 := norm_add_le (b^2) (b*(u : ℂ))
    simp only [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ u)] at h1 h2
    have hp := pow_le_pow_left₀ (norm_nonneg b) hbn 2
    have hm := mul_le_mul_of_nonneg_right hbn (by linarith : 0 ≤ u)
    nlinarith
  rw [hid]
  calc
    _ ≤ ‖4*(t : ℂ)*(b-(u : ℂ))*(b^2+b*(u : ℂ)+(u : ℂ)^2)‖+
        ‖modelDerivative t (u : ℂ)‖ := norm_add_le _ _
    _ ≤ (4*t)*L*(7*u^2)+1 := by
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht]
      gcongr
      exact real_saddle_model_residual t u hu hs
    _ = _ := by ring

theorem model_saddle_near_moving_anchor (t u L : ℝ) (z b : ℂ)
    (ht : 1 ≤ t) (hL : 0 ≤ L) (hu : 65536*(L+1) ≤ u)
    (hs : phaseSlope t u=0) (hy : z.im ≤ 1) (hb : ‖b-(u : ℂ)‖ ≤ L)
    (he : 4*(Real.pi : ℂ)*Complex.exp (4*b)=(realScale u : ℂ)+Complex.I*z) :
    ∃! w, w ∈ closedBall b (1/1024) ∧ modelDerivative t w= -(Complex.I*z) := by
  have hu1 : 1 ≤ u := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hB := real_saddle_scale_lower t u hu1 hs
  have hQ : 1 ≤ t*u^2 := by
    have hp : 1 ≤ u^2 := one_le_pow₀ hu1
    nlinarith
  have hB8 : 8 ≤ realScale u := by
    have hp : 0 ≤ t*u^3 := by positivity
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
  have hdiff : ∀ w ∈ closedBall b (1/1024), DifferentiableAt ℂ (modelDerivative t) w :=
    fun w _ => (modelDerivative_hasDerivAt t w).differentiableAt
  have hbound : ∀ w ∈ closedBall b (1/1024), ‖deriv (modelDerivative t) w-A‖ ≤ ‖A‖/2 := by
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
    have hid : deriv (modelDerivative t) w-A=
        12*(t : ℂ)*w^2+A*(Complex.exp (4*(w-b))-1) := by
      rw [(modelDerivative_hasDerivAt t w).deriv, heW]
      have h16 : 16*(Real.pi : ℂ)*Complex.exp (4*b)= -A := by
        dsimp [A]
        linear_combination 4*he
      dsimp [A] at *
      linear_combination -(Complex.exp (4*(w-b)))*h16
    have hpoly : 48*t*u^2 ≤ ‖A‖/4 := by
      have hp := mul_nonneg (show 0 ≤ 2*u-48 by linarith) (show 0 ≤ t*u^2 by positivity)
      nlinarith
    rw [hid]
    have hn := norm_add_le (12*(t : ℂ)*w^2) (A*(Complex.exp (4*(w-b))-1))
    simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0] at hn
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hwU 2)
      (show 0 ≤ 12*t by positivity)
    have hm := mul_le_mul_of_nonneg_left hexp (norm_nonneg A)
    nlinarith
  have hres := anchor_residual_bound t u L z b ht0 hu1 hL hs hb hbn he
  have hsmall : 28*L*t*u^2+1 ≤ ‖A‖/2048 := by
    have hp := mul_nonneg (show 0 ≤ 4*u-28672*L-1024 by linarith)
      (show 0 ≤ t*u^2 by positivity)
    nlinarith
  have htarget : -(Complex.I*z) ∈ closedBall (modelDerivative t b) (‖A‖*(1/1024)/2) := by
    rw [mem_closedBall, dist_eq_norm]
    have hid : -(Complex.I*z)-modelDerivative t b= -(modelDerivative t b+Complex.I*z) := by ring
    rw [hid, norm_neg]
    linarith
  obtain ⟨w,hw,hr⟩ := scalar_ball_surj (modelDerivative t) b A (1/1024)
    (by norm_num) hAn hdiff hbound htarget
  refine ⟨w, ⟨hw,hr⟩, ?_⟩
  intro v hv
  exact scalar_ball_injective (modelDerivative t) b A (1/1024) hAn hdiff hbound hv.1 hw
    (hv.2.trans hr.symm)

theorem existsUnique_transition_model_saddle (t u M : ℝ) (z : ℂ)
    (ht : 1 ≤ t) (hM : 0 ≤ M) (hu : 65536*(M+7) ≤ u)
    (hs : phaseSlope t u=0) (hy : z.im ≤ 1) (hz : ‖z‖ ≤ M*realScale u) :
    ∃! w, w ∈ closedBall (movingAnchor u z) (1/1024) ∧
      modelDerivative t w= -(Complex.I*z) := by
  have hu1 : 1 ≤ u := by linarith
  have hB : 2 ≤ realScale u := by
    have hp : 0 ≤ t*u^3 := by positivity
    linarith [real_saddle_scale_lower t u hu1 hs]
  exact model_saddle_near_moving_anchor t u (M+6) z (movingAnchor u z) ht
    (by linarith) (by linarith) hs hy (anchor_displacement u M z hB hy hM hz)
    (anchor_exponential u z hB hy)

theorem transition_model_geometry (t u M : ℝ) (z w : ℂ)
    (ht : 1 ≤ t) (hM : 0 ≤ M) (hu : 65536*(M+7) ≤ u)
    (hs : phaseSlope t u=0) (hy : z.im ≤ 1) (hz : ‖z‖ ≤ M*realScale u)
    (hw : w ∈ closedBall (movingAnchor u z) (1/1024))
    (hr : modelDerivative t w= -(Complex.I*z)) :
    ‖w-(u : ℂ)‖ ≤ M+7 ∧ 1 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
      t*w.re^3+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re := by
  have hu1 : 1 ≤ u := by linarith
  have hB : 2 ≤ realScale u := by
    have hp : 0 ≤ t*u^3 := by positivity
    linarith [real_saddle_scale_lower t u hu1 hs]
  have hd : ‖w-movingAnchor u z‖ ≤ (1/1024 : ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hw
  have hdu := anchor_displacement u M z hB hy hM hz
  have hdU : ‖w-(u : ℂ)‖ ≤ M+7 := by
    have hn := norm_add_le (w-movingAnchor u z) (movingAnchor u z-(u : ℂ))
    rw [sub_add_sub_cancel] at hn
    linarith
  have hre := Complex.abs_re_le_norm (w-(u : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  have hwre : 1 ≤ w.re := by
    have hh := (abs_le.mp (hre.trans hdU)).1
    linarith
  have hwi := Complex.abs_im_le_norm (w-movingAnchor u z)
  simp only [Complex.sub_im] at hwi
  have hwim : |w.im| ≤ 1/2 := by
    have hh := abs_add_le (w.im-(movingAnchor u z).im) (movingAnchor u z).im
    rw [sub_add_cancel] at hh
    linarith [anchor_imaginary_bound u z hB hy, Real.pi_lt_d2]
  refine ⟨hdU, hwre, hwim, ?_⟩
  have h := RiemannQuarticComplexModelSaddle.real_margin t z w (by linarith) hwre hwim hr
  linarith

theorem eventually_all_maxima_transition_model_saddle (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (RiemannQuarticDomain.weighted 0 t 0) (Ici 0) u →
      ∀ z : ℂ, z.im ≤ 1 → ‖z‖ ≤ M*realScale u →
        ∃! w, w ∈ closedBall (movingAnchor u z) (1/1024) ∧
          modelDerivative t w= -(Complex.I*z) := by
  filter_upwards [RiemannQuarticRealSaddle.maxima_escape (65536*(M+7)) (by positivity),
    eventually_ge_atTop (1 : ℝ)] with t hU ht
  intro u hu hm z hy hz
  have huU := (hU u hu hm).le
  have hu0 : 0 < u := by linarith
  have hs := RiemannQuarticRealSaddle.max_real_stationary t u hu0 hm
  rw [← (RiemannQuarticRealSaddle.kernel_hasDerivAt u).deriv] at hs
  exact existsUnique_transition_model_saddle t u M z ht hM huU hs hy hz

theorem eventually_exists_transition_family (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, 65536*(M+7) ≤ u ∧ phaseSlope t u=0 ∧
      ∀ z : ℂ, z.im ≤ 1 → ‖z‖ ≤ M*realScale u →
        ∃! w, w ∈ closedBall (movingAnchor u z) (1/1024) ∧
          modelDerivative t w= -(Complex.I*z) := by
  filter_upwards [RiemannQuarticRealSaddle.maxima_escape (65536*(M+7)) (by positivity),
    eventually_all_maxima_transition_model_saddle M hM] with t hU hmodels
  obtain ⟨u,hu,hm⟩ := RiemannQuarticRealSaddle.exists_global_max t
  have huU := (hU u hu hm).le
  have hu0 : 0 < u := by linarith
  have hs := RiemannQuarticRealSaddle.max_real_stationary t u hu0 hm
  rw [← (RiemannQuarticRealSaddle.kernel_hasDerivAt u).deriv] at hs
  exact ⟨u, huU, hs, hmodels u hu hm⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionSaddle
