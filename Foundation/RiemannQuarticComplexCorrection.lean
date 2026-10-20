import Foundation.RiemannQuarticComplexModelSaddle
import Foundation.RiemannQuarticFarCorrection
/-! Actual arithmetic saddle correction at large complex frequencies.
Lower-half-plane model roots have quantitative theta-domain margins.
The scalar inverse constructs actual roots for every nearby complex frequency.
This is not a full signed Fourier remainder or a zero-exclusion theorem. -/
noncomputable section
open Set Metric Complex Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticComplexCorrection
open RiemannQuarticSaddleTheta RiemannQuarticFarModelSaddle
open RiemannQuarticSaddleBranch RiemannThetaComplexKernel
open RiemannQuarticFarCorrection

theorem model_exp_norm_le_frequency (t : ℝ) (z : ℂ) (ht : 0 ≤ t) (hx : 0 < ‖z‖) (w : ℂ)
    (hpoly : 4*t*‖w‖^3+9 ≤ ‖z‖) (hs : modelDerivative t w= -(Complex.I*z)) :
    ‖Complex.exp (4*w)‖ ≤ ‖z‖ := by
  have he : 4*(Real.pi : ℂ)*Complex.exp (4*w)=4*(t : ℂ)*w^3+9+Complex.I*z := by
    unfold modelDerivative at hs
    linear_combination -hs
  have hn := congrArg norm he
  have h1 := norm_add_le (4*(t : ℂ)*w^3+9) (Complex.I*z)
  have h2 := norm_add_le (4*(t : ℂ)*w^3) (9 : ℂ)
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht,abs_of_pos Real.pi_pos,Complex.norm_I,one_mul] at hn h1 h2
  nlinarith [norm_nonneg (Complex.exp (4*w)),Real.pi_gt_three]


theorem neighbor_domain (t : ℝ) (z : ℂ) (hz : z.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖z‖) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*z))
    (hp : 4*t*‖w‖^3+9 ≤ ‖z‖) (hv : ‖v-w‖ ≤ 2/‖z‖) :
    0 ≤ v.re ∧ 1 ≤ (Complex.exp (4*v)).re ∧
      (t*w.re^3-z.im)/32 ≤ (Complex.exp (4*v)).re := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < ‖z‖ := by linarith
  have hE := model_exp_norm_le_frequency t z ht0 hx0 w hp hs
  have hn := neighbor_real_margin ‖z‖ hx w v hE hv
  have hlow := RiemannQuarticComplexModelSaddle.real_margin t z w ht0 (by linarith) hi hs
  have htr0 : 0 ≤ t*w.re^3 := by positivity
  have hR0 : 0 ≤ (Complex.exp (4*w)).re := by nlinarith [Real.pi_pos]
  have hp4 := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hR0
  have hcub : 32768 ≤ w.re^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤32) hr 3
    norm_num at h
    exact h
  have htcub : w.re^3 ≤ t*w.re^3 := by nlinarith
  have hd : ‖v-w‖ ≤ 1 := by
    have hq : 2/‖z‖ ≤ 1 := (div_le_iff₀ hx0).mpr (by linarith)
    exact hv.trans hq
  have hcoord := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hcoord
  refine ⟨?_,?_,?_⟩
  · linarith [(abs_le.mp hcoord).1]
  · nlinarith
  · nlinarith


theorem neighbor_error_bound (t : ℝ) (z : ℂ) (hz : z.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖z‖) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*z))
    (hp : 4*t*‖w‖^3+9 ≤ ‖z‖) (hv : ‖v-w‖ ≤ 2/‖z‖) :
    ‖complexSlope t v-modelDerivative t v‖ ≤ 30005*Real.exp (-w.re) := by
  have hdom := neighbor_domain t z hz ht hx w v hr hi hs hp hv
  have hd : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ (by linarith : 0 < ‖z‖)).mpr (by linarith))
  have hcoord := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hcoord
  have hlo := (abs_le.mp hcoord).1
  have hhi := (abs_le.mp hcoord).2
  have heq : complexSlope t v-modelDerivative t v=
      kernelDerivative v/kernelComplex v-(9-4*(Real.pi : ℂ)*Complex.exp (4*v)) := by
    unfold complexSlope modelDerivative
    rw [(kernelComplex_hasDerivAt v (by linarith [hdom.2.1])).deriv]
    ring
  rw [heq]
  apply (RiemannQuarticSaddleNeighborhood.logDerivative_coarse_bound v hdom.1 hdom.2.1).trans
  have hcub : 1024*w.re ≤ w.re^3 := by
    have hsq : 1024 ≤ w.re^2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)
    nlinarith
  have htcub : w.re^3 ≤ t*w.re^3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 3]
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by linarith [hdom.2.1] : 0 ≤ (Complex.exp (4*v)).re)
  have h1 : Real.exp (-4*v.re) ≤ Real.exp (-w.re) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (4*v.re)*Real.exp (-3*Real.pi*(Complex.exp (4*v)).re) ≤ Real.exp (-w.re) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hdom.2.2]
  have hh1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ)≤5)
  have hh2 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ)≤30000)
  nlinarith




theorem neighbor_slope_analytic (t : ℝ) (z : ℂ) (hz : z.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖z‖) (w : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*z))
    (hp : 4*t*‖w‖^3+9 ≤ ‖z‖) :
    AnalyticOnNhd ℂ (complexSlope t) (closedBall w (2/‖z‖)) := by
  intro v hv
  have hd : ‖v-w‖ ≤ 2/‖z‖ := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hdom := neighbor_domain t z hz ht hx w v hr hi hs hp hd
  have ha := kernelComplex_analyticAt v (by linarith [hdom.2.1])
  have hn := kernel_ne_zero v hdom.1 hdom.2.1
  exact (analyticAt_const.mul (analyticAt_id.pow 3)).add (ha.deriv.div ha hn)


theorem neighbor_error_deriv_bound (t : ℝ) (z : ℂ) (hz : z.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖z‖) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*z))
    (hp : 4*t*‖w‖^3+9 ≤ ‖z‖) (hv : v ∈ closedBall w (1/‖z‖)) :
    ‖deriv (complexSlope t) v-deriv (modelDerivative t) v‖ ≤
      (30005*Real.exp (-w.re))*‖z‖ := by
  have hx0 : 0 < ‖z‖ := by linarith
  have hsub : closedBall v (1/‖z‖) ⊆ closedBall w (2/‖z‖) := by
    intro u hu
    have h := dist_triangle u v w
    have hz' := mem_closedBall.mp hu
    have hv' := mem_closedBall.mp hv
    apply mem_closedBall.mpr
    have htwo : 1/‖z‖+1/‖z‖=2/‖z‖ := by ring
    linarith
  have ha := neighbor_slope_analytic t z hz ht hx w hr hi hs hp
  have hm : AnalyticOnNhd ℂ (modelDerivative t) (closedBall w (2/‖z‖)) := by
    intro z _
    unfold modelDerivative
    fun_prop
  have hd := ((ha.sub hm).mono hsub).differentiableOn.diffContOnCl_ball (Subset.refl _)
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by positivity : (0 : ℝ)<1/‖z‖) hd (fun u hu => neighbor_error_bound t z hz ht hx w u hr hi hs hp
      (by simpa only [mem_closedBall,dist_eq_norm] using hsub (sphere_subset_closedBall hu)))
  have hvin : v ∈ closedBall w (2/‖z‖) := hsub (mem_closedBall_self (by positivity))
  rw [deriv_sub (ha v hvin).differentiableAt (modelDerivative_hasDerivAt t v).differentiableAt] at h
  simpa only [one_div,div_inv_eq_mul] using h



theorem model_deriv_near_far_saddle (t : ℝ) (z : ℂ) (ht : 1 ≤ t) (hx : 10000 ≤ ‖z‖) (w v : ℂ)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖z‖)
    (hs : modelDerivative t w= -(Complex.I*z)) (hv : ‖v-w‖ ≤ 1/‖z‖) :
    ‖deriv (modelDerivative t) v-(-(4 : ℂ)*Complex.I*z)‖ ≤ ‖z‖ := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < ‖z‖ := by linarith
  let M := ‖w‖+1
  have hM : 1 ≤ M := by dsimp [M]; linarith [norm_nonneg w]
  have hM0 : 0 ≤ M := by linarith
  have hM23 : M^2 ≤ M^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sq_nonneg M)]
  have hwM : ‖w‖ ≤ M := by dsimp [M]; linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) hwM 3
  have hpol : 4*t*‖w‖^3+9 ≤ ‖z‖ := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    change 100*(t*M^3+1) ≤ ‖z‖ at hp
    nlinarith [pow_nonneg hM0 3]
  have hE := model_exp_norm_le_frequency t z ht0 hx0 w hpol hs
  have hv2 : ‖v-w‖ ≤ 2/‖z‖ := hv.trans (by apply (div_le_div_iff_of_pos_right hx0).mpr; norm_num)
  have hsmall : 4*‖v-w‖ ≤ 1 := by
    have hq : 1/‖z‖ ≤ (1/4 : ℝ) := (div_le_iff₀ hx0).mpr (by linarith)
    linarith
  have herr := exp4_difference_bound w v hsmall
  have hmul := mul_le_mul hE hv (norm_nonneg _) hx0.le
  have hcancel : ‖z‖*(1/‖z‖)=1 := by field_simp
  have he8 : ‖Complex.exp (4*v)-Complex.exp (4*w)‖ ≤ 8 := by nlinarith
  have hv1 : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hvM : ‖v‖ ≤ M := by
    have h := norm_add_le (v-w) w
    rw [sub_add_cancel] at h
    dsimp [M]
    linarith
  have heq : 4*(Real.pi : ℂ)*Complex.exp (4*w)=4*(t : ℂ)*w^3+9+Complex.I*z := by
    unfold modelDerivative at hs
    linear_combination -hs
  have hid : deriv (modelDerivative t) v-(-(4 : ℂ)*Complex.I*z)=
      (12*(t : ℂ)*v^2-16*(t : ℂ)*w^3-36)-
        16*(Real.pi : ℂ)*(Complex.exp (4*v)-Complex.exp (4*w)) := by
    rw [(modelDerivative_hasDerivAt t v).deriv]
    linear_combination -4*heq
  rw [hid]
  have h1 := norm_sub_le (12*(t : ℂ)*v^2-16*(t : ℂ)*w^3-36)
    (16*(Real.pi : ℂ)*(Complex.exp (4*v)-Complex.exp (4*w)))
  have h2 := norm_sub_le (12*(t : ℂ)*v^2-16*(t : ℂ)*w^3) (36 : ℂ)
  have h3 := norm_sub_le (12*(t : ℂ)*v^2) (16*(t : ℂ)*w^3)
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht0,abs_of_pos Real.pi_pos] at h1 h2 h3
  have hvpow := pow_le_pow_left₀ (norm_nonneg v) hvM 2
  have hvm := mul_le_mul_of_nonneg_left (hvpow.trans hM23) ht0
  have hwm := mul_le_mul_of_nonneg_left hpw ht0
  have hpie := mul_le_mul Real.pi_lt_four.le he8 (norm_nonneg _) (by norm_num : (0 : ℝ)≤4)
  change 100*(t*M^3+1) ≤ ‖z‖ at hp
  nlinarith



theorem actual_far_frequency_disk (t : ℝ) (z : ℂ) (hz : z.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖z‖) (w : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖z‖)
    (hs : modelDerivative t w= -(Complex.I*z))
    (q : ℂ) (hq : ‖q-z‖ ≤ 1) :
    ∃! v, v ∈ closedBall w (1/‖z‖) ∧ complexSlope t v= -(Complex.I*q) := by
  have hx0 : 0 < ‖z‖ := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hpol : 4*t*‖w‖^3+9 ≤ ‖z‖ := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 3]
  have hsmall := small_error_at_large_real_part w.re hr
  have ha := neighbor_slope_analytic t z hz ht (by linarith) w (by linarith) hi hs hpol
  let A := -(4 : ℂ)*Complex.I*z
  have hA : ‖A‖=4*‖z‖ := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,mul_one]
  have hAn : A ≠ 0 := norm_pos_iff.mp (by rw [hA]; positivity)
  have hsub : closedBall w (1/‖z‖) ⊆ closedBall w (2/‖z‖) :=
    closedBall_subset_closedBall (by apply (div_le_div_iff_of_pos_right hx0).mpr; norm_num)
  have hd : ∀ v ∈ closedBall w (1/‖z‖), DifferentiableAt ℂ (complexSlope t) v :=
    fun v hv => (ha v (hsub hv)).differentiableAt
  have hb : ∀ v ∈ closedBall w (1/‖z‖), ‖deriv (complexSlope t) v-A‖ ≤ ‖A‖/2 := by
    intro v hv
    have h1 := neighbor_error_deriv_bound t z hz ht (by linarith) w v (by linarith) hi hs hpol hv
    have h2 := model_deriv_near_far_saddle t z ht hx w v hp hs
      (by simpa only [mem_closedBall,dist_eq_norm] using hv)
    have h3 := norm_add_le (deriv (complexSlope t) v-deriv (modelDerivative t) v)
      (deriv (modelDerivative t) v-A)
    rw [sub_add_sub_cancel] at h3
    have hm := mul_le_mul_of_nonneg_right hsmall hx0.le
    rw [hA]
    change ‖deriv (modelDerivative t) v-A‖ ≤ ‖z‖ at h2
    nlinarith
  have hres := neighbor_error_bound t z hz ht (by linarith) w w (by linarith) hi hs hpol
    (by simp; positivity)
  have htarget : -(Complex.I*q) ∈ closedBall (complexSlope t w) (‖A‖*(1/‖z‖)/2) := by
    rw [mem_closedBall,dist_eq_norm,hA]
    have hid : -(Complex.I*q)-complexSlope t w=
        -(Complex.I*(q-z))-(complexSlope t w-modelDerivative t w) := by rw [hs]; ring
    rw [hid]
    have htri := norm_sub_le (-(Complex.I*(q-z))) (complexSlope t w-modelDerivative t w)
    simp only [norm_neg,norm_mul,Complex.norm_I,one_mul] at htri
    have hcancel : 4*‖z‖*(1/‖z‖)/2=2 := by field_simp; ring
    rw [hcancel]
    linarith
  obtain ⟨v,hv,hroot⟩ := RiemannQuarticQuantitativeSaddle.scalar_ball_surj
    (complexSlope t) w A (1/‖z‖) (by positivity) hAn hd hb htarget
  refine ⟨v,⟨hv,hroot⟩,?_⟩
  intro q hz
  exact RiemannQuarticQuantitativeSaddle.scalar_ball_injective
    (complexSlope t) w A (1/‖z‖) hAn hd hb hz.1 hv (hz.2.trans hroot.symm)



theorem actual_far_saddle (t : ℝ) (z : ℂ) (hz : z.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖z‖) (w : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖z‖)
    (hs : modelDerivative t w= -(Complex.I*z)) :
    ∃! v, v ∈ closedBall w (1/‖z‖) ∧ complexSlope t v= -(Complex.I*z) :=
  actual_far_frequency_disk t z hz ht hx w hr hi hp hs z (by simp)


theorem corrected_saddle_geometry (t : ℝ) (z : ℂ) (hz : z.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖z‖) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖z‖)
    (hs : modelDerivative t w= -(Complex.I*z)) (hv : v ∈ closedBall w (1/‖z‖)) :
    1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 := by
  have hx0 : 0 < ‖z‖ := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hpol : 4*t*‖w‖^3+9 ≤ ‖z‖ := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 3]
  have hdist : ‖v-w‖ ≤ 1/‖z‖ := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hd2 : ‖v-w‖ ≤ 2/‖z‖ := hdist.trans (by apply (div_le_div_iff_of_pos_right hx0).mpr; norm_num)
  have hdom := neighbor_domain t z hz ht (by linarith) w v (by linarith) hi hs hpol hd2
  have hd1 : ‖v-w‖ ≤ 1/2 := hdist.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hre := (Complex.abs_re_le_norm (v-w)).trans hd1
  have him := (Complex.abs_im_le_norm (v-w)).trans hd1
  simp only [Complex.sub_re,Complex.sub_im] at hre him
  have hiv : |v.im| ≤ 1 := by
    apply abs_le.mpr
    rcases abs_le.mp hi with ⟨hi1,hi2⟩
    rcases abs_le.mp him with ⟨hv1,hv2⟩
    constructor <;> linarith
  have hpos : 0 < Real.cos (4*v.im) := by
    have he : (Complex.exp (4*v)).re=Real.exp (4*v.re)*Real.cos (4*v.im) := by
      simp [Complex.exp_re,Complex.mul_re,Complex.mul_im]
    have hp : 0 < (Complex.exp (4*v)).re := by linarith [hdom.2.1]
    rw [he] at hp
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hp
  have hlt : |4*v.im| < Real.pi/2 := by
    by_contra hn
    have hh := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt hn)
      (by rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<4)]; linarith [Real.pi_gt_three] :
        |4*v.im| ≤ Real.pi+Real.pi/2)
    rw [Real.cos_abs] at hh
    linarith
  refine ⟨?_,?_,kernel_ne_zero v hdom.1 hdom.2.1⟩
  · linarith [(abs_le.mp hre).1]
  · rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<4)] at hlt
    linarith


theorem actual_far_deriv_norm_lower (t : ℝ) (z : ℂ) (hz : z.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖z‖) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖z‖)
    (hs : modelDerivative t w= -(Complex.I*z)) (hv : v ∈ closedBall w (1/‖z‖)) :
    2*‖z‖ ≤ ‖deriv (complexSlope t) v‖ := by
  have hx0 : 0 < ‖z‖ := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hpol : 4*t*‖w‖^3+9 ≤ ‖z‖ := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 3]
  let A := -(4 : ℂ)*Complex.I*z
  have hA : ‖A‖=4*‖z‖ := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,mul_one]
  have h1 := neighbor_error_deriv_bound t z hz ht (by linarith) w v (by linarith) hi hs hpol hv
  have h2 := model_deriv_near_far_saddle t z ht hx w v hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have hsmall := mul_le_mul_of_nonneg_right (small_error_at_large_real_part w.re hr) hx0.le
  have h3 := norm_add_le (deriv (complexSlope t) v-deriv (modelDerivative t) v)
    (deriv (modelDerivative t) v-A)
  rw [sub_add_sub_cancel] at h3
  change ‖deriv (modelDerivative t) v-A‖ ≤ ‖z‖ at h2
  have h4 := norm_sub_le (deriv (complexSlope t) v) (deriv (complexSlope t) v-A)
  rw [sub_sub_cancel,hA] at h4
  nlinarith


theorem eventually_actual_half_circles (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ a : ℝ in atTop, ∀ z : ℂ, z.im ≤ 0 →
      ‖z‖ = 4*Real.pi*Real.exp (4*a) → ∃ w v : ℂ,
        w ∈ closedBall (RiemannQuarticComplexModelSaddle.complexAnchor z) (1/1024) ∧
        modelDerivative t w = -(Complex.I*z) ∧
        v ∈ closedBall w (1/‖z‖) ∧ complexSlope t v = -(Complex.I*z) ∧
        1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 ∧
        1 ≤ (Complex.exp (4*v)).re ∧ 2*‖z‖ ≤ ‖deriv (complexSlope t) v‖ := by
  have ht0 : 0 ≤ t := by linarith
  filter_upwards [RiemannQuarticComplexModelSaddle.eventually_lower_half_circles t ht0,
    RiemannQuarticDomain.quartic_exponent_dominated (80000*(t+1)) 0,
    eventually_ge_atTop (240040 : ℝ)] with a hex hdom ha
  intro z hz hn
  obtain ⟨w,hw,hs,hwr,hwi,hmargin⟩ := hex z hz hn
  have ha0 : 0 ≤ a := by linarith
  have hp3 := pow_le_pow_left₀ (by linarith : 0 ≤ a+3) (by linarith : a+3 ≤ 2*a) 3
  have hp34 : a^3 ≤ a^4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ a-1) (pow_nonneg ha0 3)]
  have hM : (a+3)^3 ≤ 8*a^4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 10000*(t+1))
  simp only [zero_mul,add_zero] at hdom
  have hscale : 10000*(t+1)*(a+3)^3 ≤ ‖z‖ := by
    rw [hn]
    nlinarith [Real.pi_gt_three,Real.exp_pos (4*a)]
  have hM1 : 1 ≤ (a+3)^3 := one_le_pow₀ (by linarith)
  have hx : 10000 ≤ ‖z‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hM1 (by positivity : 0 ≤ t+1)]
  have hd : ‖w-RiemannQuarticComplexModelSaddle.complexAnchor z‖ ≤ (1/1024 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hw
  have hreal := (Complex.abs_re_le_norm (w-RiemannQuarticComplexModelSaddle.complexAnchor z)).trans hd
  have hg := RiemannQuarticComplexModelSaddle.complexAnchor_geometry a ha0 z hz hn
  simp only [Complex.sub_re,hg.1] at hreal
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hreal).1]
  have hnorm : ‖w‖+1 ≤ a+3 := by
    have hb := norm_add_le (w-RiemannQuarticComplexModelSaddle.complexAnchor z)
      (RiemannQuarticComplexModelSaddle.complexAnchor z)
    rw [sub_add_cancel] at hb
    linarith [hg.2.2]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖+1) hnorm 3
  have hps : 100*(t*(‖w‖+1)^3+1) ≤ ‖z‖ := by
    have hmul := mul_le_mul_of_nonneg_left hpow ht0
    nlinarith [pow_nonneg (by linarith : 0 ≤ a+3) 3]
  have hi : |w.im| ≤ 1/2 := by linarith [Real.pi_lt_four]
  obtain ⟨v,⟨hv,hroot⟩,_⟩ := actual_far_saddle t z hz ht hx w hr hi hps hs
  have hgeom := corrected_saddle_geometry t z hz ht hx w v hr hi hps hs hv
  have hderiv := actual_far_deriv_norm_lower t z hz ht hx w v hr hi hps hs hv
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hpol : 4*t*‖w‖^3+9 ≤ ‖z‖ := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 3]
  have hv2 : ‖v-w‖ ≤ 2/‖z‖ := by
    have hd := mem_closedBall.mp hv
    rw [dist_eq_norm] at hd
    have hx0 : 0 < ‖z‖ := by linarith
    exact hd.trans (by apply (div_le_div_iff_of_pos_right hx0).mpr; norm_num)
  have hdom := neighbor_domain t z hz ht (by linarith) w v (by linarith) hi hs hpol hv2
  exact ⟨w,v,hw,hs,hv,hroot,hgeom.1,hgeom.2.1,hgeom.2.2,hdom.2.1,hderiv⟩

theorem far_lower_half_plane_actual (t : ℝ) (ht : 1 ≤ t) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → z.im ≤ 0 → ∃ v : ℂ,
      complexSlope t v = -(Complex.I*z) ∧
      1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 ∧
      1 ≤ (Complex.exp (4*v)).re ∧ 2*‖z‖ ≤ ‖deriv (complexSlope t) v‖ ∧
      HasDerivAt (RiemannQuarticFrequencyBranch.saddleWeight t z) 0 v ∧
      RiemannQuarticFrequencyBranch.saddleWeight t z v ≠ 0 ∧
      RiemannQuarticFlow.flow t z =
        ((∫ s : ℝ in Ioi 0, RiemannQuarticFrequencyBranch.saddleWeight t z
          ((s : ℂ)+(v.im : ℂ)*Complex.I))+
         (∫ s : ℝ in Ioi 0, RiemannQuarticFrequencyBranch.saddleWeight t (-z)
          ((s : ℂ)-(v.im : ℂ)*Complex.I)))/2 := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (eventually_actual_half_circles t ht)
  let R := 4*Real.pi*Real.exp (4*A)
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R,hR,?_⟩
  intro z hz him
  have hn0 : 0 < ‖z‖ := hR.trans_le hz
  let a := Real.log (‖z‖/(4*Real.pi))/4
  have hq : 0 < ‖z‖/(4*Real.pi) := by positivity
  have hn : ‖z‖ = 4*Real.pi*Real.exp (4*a) := by
    rw [show 4*a = Real.log (‖z‖/(4*Real.pi)) by dsimp [a]; ring,Real.exp_log hq]
    field_simp
  have hAa : A ≤ a := by
    have he : Real.exp (4*A) ≤ Real.exp (4*a) := by
      rw [hn] at hz
      change 4*Real.pi*Real.exp (4*A) ≤ 4*Real.pi*Real.exp (4*a) at hz
      exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4*Real.pi)).mp hz
    have hh := Real.exp_le_exp.mp he
    linarith
  obtain ⟨w,v,hw,hs,hv,hroot,hr,hi,hkn,hE,hd⟩ := hA a hAa z him hn
  have hc := actual_weight_critical t z v (by linarith) hkn hroot
  exact ⟨v,hroot,hr,hi,hkn,hE,hd,hc.1,hc.2,
    RiemannQuarticNaturalContour.flow_eq_paired_horizontal t z v.im hi⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticComplexCorrection
