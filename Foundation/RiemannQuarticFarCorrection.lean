import Foundation.RiemannQuarticFarModelSaddle
/-! Actual high-frequency quartic Xi saddles corrected from constructed model roots.
Shrinking 2/x neighborhoods retain the arithmetic theta-kernel domain; Cauchy
controls actual/model derivative error. A quantitative inverse corrects every
frequency in a unit complex disk. Each fixed t >= 1 has actual saddles at all
sufficiently large real frequencies, with exact signed contours through their
heights. No uniform-in-t far-field asymptotic or global zero conclusion follows.
The deliberately conservative large-real-part cutoff is not optimized. -/
noncomputable section
open Set Metric Complex
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarCorrection
open RiemannQuarticSaddleTheta

theorem exp4_difference_bound (w v : ℂ) (hsmall : 4*‖v-w‖ ≤ 1) :
    ‖Complex.exp (4*v)-Complex.exp (4*w)‖ ≤ 8*‖Complex.exp (4*w)‖*‖v-w‖ := by
  have he := Complex.norm_exp_sub_one_le (x := 4*(v-w)) (by
    simpa only [norm_mul,Complex.norm_ofNat] using hsmall)
  have hid : Complex.exp (4*v)-Complex.exp (4*w)=
      Complex.exp (4*w)*(Complex.exp (4*(v-w))-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 2
    ring
  rw [hid,norm_mul]
  rw [norm_mul,Complex.norm_ofNat] at he
  nlinarith [mul_le_mul_of_nonneg_left he (norm_nonneg (Complex.exp (4*w)))]

theorem model_exp_norm_le_frequency (t x : ℝ) (ht : 0 ≤ t) (hx : 0 < x) (w : ℂ)
    (hpoly : 4*t*‖w‖^3+9 ≤ x) (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) :
    ‖Complex.exp (4*w)‖ ≤ x := by
  have he : 4*(Real.pi : ℂ)*Complex.exp (4*w)=4*(t : ℂ)*w^3+9+Complex.I*(x : ℂ) := by
    unfold modelDerivative at hs
    linear_combination -hs
  have hn := congrArg norm he
  have h1 := norm_add_le (4*(t : ℂ)*w^3+9) (Complex.I*(x : ℂ))
  have h2 := norm_add_le (4*(t : ℂ)*w^3) (9 : ℂ)
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht,abs_of_pos hx,abs_of_pos Real.pi_pos,Complex.norm_I,one_mul] at hn h1 h2
  nlinarith [norm_nonneg (Complex.exp (4*w)),Real.pi_gt_three]

theorem neighbor_real_margin (x : ℝ) (hx : 8 ≤ x) (w v : ℂ)
    (hE : ‖Complex.exp (4*w)‖ ≤ x) (hv : ‖v-w‖ ≤ 2/x) :
    (Complex.exp (4*w)).re-16 ≤ (Complex.exp (4*v)).re := by
  have hx0 : 0 < x := by linarith
  have hsmall : 4*‖v-w‖ ≤ 1 := by
    have hq : 2/x ≤ (1/4 : ℝ) := by apply (div_le_iff₀ hx0).mpr; linarith
    linarith
  have h := exp4_difference_bound w v hsmall
  have hmul := mul_le_mul hE hv (norm_nonneg _) hx0.le
  have hcancel : 8*x*(2/x)=16 := by field_simp; norm_num
  have hbound : ‖Complex.exp (4*v)-Complex.exp (4*w)‖ ≤ 16 := by nlinarith
  have hr := (Complex.abs_re_le_norm (Complex.exp (4*v)-Complex.exp (4*w))).trans hbound
  simp only [Complex.sub_re] at hr
  linarith [(abs_le.mp hr).1]



open RiemannQuarticFarModelSaddle RiemannQuarticSaddleBranch RiemannThetaComplexKernel

theorem neighbor_domain (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 2/x) :
    0 ≤ v.re ∧ 1 ≤ (Complex.exp (4*v)).re ∧
      t*w.re^3/32 ≤ (Complex.exp (4*v)).re := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  have hE := model_exp_norm_le_frequency t x ht0 hx0 w hp hs
  have hn := neighbor_real_margin x hx w v hE hv
  have hlow := saddle_real_lower t x w ht0 (by linarith) hi hs
  have htr0 : 0 ≤ t*w.re^3 := by positivity
  have hR0 : 0 ≤ (Complex.exp (4*w)).re := by nlinarith [Real.pi_pos]
  have hp4 := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hR0
  have hcub : 32768 ≤ w.re^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤32) hr 3
    norm_num at h
    exact h
  have htcub : w.re^3 ≤ t*w.re^3 := by nlinarith
  have hd : ‖v-w‖ ≤ 1 := by
    have hq : 2/x ≤ 1 := (div_le_iff₀ hx0).mpr (by linarith)
    exact hv.trans hq
  have hcoord := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hcoord
  refine ⟨?_,?_,?_⟩
  · linarith [(abs_le.mp hcoord).1]
  · nlinarith
  · nlinarith

theorem neighbor_error_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : ‖v-w‖ ≤ 2/x) :
    ‖complexSlope t v-modelDerivative t v‖ ≤ 30005*Real.exp (-w.re) := by
  have hdom := neighbor_domain t x ht hx w v hr hi hs hp hv
  have hd : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ (by linarith : 0 < x)).mpr (by linarith))
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



theorem neighbor_slope_analytic (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) :
    AnalyticOnNhd ℂ (complexSlope t) (closedBall w (2/x)) := by
  intro v hv
  have hd : ‖v-w‖ ≤ 2/x := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hdom := neighbor_domain t x ht hx w v hr hi hs hp hd
  have ha := kernelComplex_analyticAt v (by linarith [hdom.2.1])
  have hn := kernel_ne_zero v hdom.1 hdom.2.1
  exact (analyticAt_const.mul (analyticAt_id.pow 3)).add (ha.deriv.div ha hn)

theorem neighbor_error_deriv_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 4*t*‖w‖^3+9 ≤ x) (hv : v ∈ closedBall w (1/x)) :
    ‖deriv (complexSlope t) v-deriv (modelDerivative t) v‖ ≤
      (30005*Real.exp (-w.re))*x := by
  have hx0 : 0 < x := by linarith
  have hsub : closedBall v (1/x) ⊆ closedBall w (2/x) := by
    intro z hz
    have h := dist_triangle z v w
    have hz' := mem_closedBall.mp hz
    have hv' := mem_closedBall.mp hv
    apply mem_closedBall.mpr
    have htwo : 1/x+1/x=2/x := by ring
    linarith
  have ha := neighbor_slope_analytic t x ht hx w hr hi hs hp
  have hm : AnalyticOnNhd ℂ (modelDerivative t) (closedBall w (2/x)) := by
    intro z _
    unfold modelDerivative
    fun_prop
  have hd := ((ha.sub hm).mono hsub).differentiableOn.diffContOnCl_ball (Subset.refl _)
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by positivity : (0 : ℝ)<1/x) hd (fun z hz => neighbor_error_bound t x ht hx w z hr hi hs hp
      (by simpa only [mem_closedBall,dist_eq_norm] using hsub (sphere_subset_closedBall hz)))
  have hvin : v ∈ closedBall w (2/x) := hsub (mem_closedBall_self (by positivity))
  rw [deriv_sub (ha v hvin).differentiableAt (modelDerivative_hasDerivAt t v).differentiableAt] at h
  simpa only [one_div,div_inv_eq_mul] using h


theorem model_deriv_near_far_saddle (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w v : ℂ)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) (hv : ‖v-w‖ ≤ 1/x) :
    ‖deriv (modelDerivative t) v-(-(4 : ℂ)*Complex.I*(x : ℂ))‖ ≤ x := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  let M := ‖w‖+1
  have hM : 1 ≤ M := by dsimp [M]; linarith [norm_nonneg w]
  have hM0 : 0 ≤ M := by linarith
  have hM23 : M^2 ≤ M^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sq_nonneg M)]
  have hwM : ‖w‖ ≤ M := by dsimp [M]; linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) hwM 3
  have hpol : 4*t*‖w‖^3+9 ≤ x := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    change 100*(t*M^3+1) ≤ x at hp
    nlinarith [pow_nonneg hM0 3]
  have hE := model_exp_norm_le_frequency t x ht0 hx0 w hpol hs
  have hv2 : ‖v-w‖ ≤ 2/x := hv.trans (by apply (div_le_div_iff_of_pos_right hx0).mpr; norm_num)
  have hsmall : 4*‖v-w‖ ≤ 1 := by
    have hq : 1/x ≤ (1/4 : ℝ) := (div_le_iff₀ hx0).mpr (by linarith)
    linarith
  have herr := exp4_difference_bound w v hsmall
  have hmul := mul_le_mul hE hv (norm_nonneg _) hx0.le
  have hcancel : x*(1/x)=1 := by field_simp
  have he8 : ‖Complex.exp (4*v)-Complex.exp (4*w)‖ ≤ 8 := by nlinarith
  have hv1 : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hvM : ‖v‖ ≤ M := by
    have h := norm_add_le (v-w) w
    rw [sub_add_cancel] at h
    dsimp [M]
    linarith
  have heq : 4*(Real.pi : ℂ)*Complex.exp (4*w)=4*(t : ℂ)*w^3+9+Complex.I*(x : ℂ) := by
    unfold modelDerivative at hs
    linear_combination -hs
  have hid : deriv (modelDerivative t) v-(-(4 : ℂ)*Complex.I*(x : ℂ))=
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
  change 100*(t*M^3+1) ≤ x at hp
  nlinarith


theorem small_error_at_large_real_part (r : ℝ) (hr : 120020 ≤ r) :
    30005*Real.exp (-r) ≤ (1/4 : ℝ) := by
  have h := Real.add_one_le_exp r
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (-r)).le
  have hid : Real.exp r*Real.exp (-r)=1 := by rw [← Real.exp_add]; simp
  rw [hid] at hm
  nlinarith [Real.exp_pos (-r)]

theorem actual_far_frequency_disk (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    ∃! v, v ∈ closedBall w (1/x) ∧ complexSlope t v= -(Complex.I*z) := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hpol : 4*t*‖w‖^3+9 ≤ x := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 3]
  have hsmall := small_error_at_large_real_part w.re hr
  have ha := neighbor_slope_analytic t x ht (by linarith) w (by linarith) hi hs hpol
  let A := -(4 : ℂ)*Complex.I*(x : ℂ)
  have hA : ‖A‖=4*x := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0,mul_one]
  have hAn : A ≠ 0 := norm_pos_iff.mp (by rw [hA]; positivity)
  have hsub : closedBall w (1/x) ⊆ closedBall w (2/x) :=
    closedBall_subset_closedBall (by apply (div_le_div_iff_of_pos_right hx0).mpr; norm_num)
  have hd : ∀ v ∈ closedBall w (1/x), DifferentiableAt ℂ (complexSlope t) v :=
    fun v hv => (ha v (hsub hv)).differentiableAt
  have hb : ∀ v ∈ closedBall w (1/x), ‖deriv (complexSlope t) v-A‖ ≤ ‖A‖/2 := by
    intro v hv
    have h1 := neighbor_error_deriv_bound t x ht (by linarith) w v (by linarith) hi hs hpol hv
    have h2 := model_deriv_near_far_saddle t x ht hx w v hp hs
      (by simpa only [mem_closedBall,dist_eq_norm] using hv)
    have h3 := norm_add_le (deriv (complexSlope t) v-deriv (modelDerivative t) v)
      (deriv (modelDerivative t) v-A)
    rw [sub_add_sub_cancel] at h3
    have hm := mul_le_mul_of_nonneg_right hsmall hx0.le
    rw [hA]
    change ‖deriv (modelDerivative t) v-A‖ ≤ x at h2
    nlinarith
  have hres := neighbor_error_bound t x ht (by linarith) w w (by linarith) hi hs hpol
    (by simp; positivity)
  have htarget : -(Complex.I*z) ∈ closedBall (complexSlope t w) (‖A‖*(1/x)/2) := by
    rw [mem_closedBall,dist_eq_norm,hA]
    have hid : -(Complex.I*z)-complexSlope t w=
        -(Complex.I*(z-(x : ℂ)))-(complexSlope t w-modelDerivative t w) := by rw [hs]; ring
    rw [hid]
    have htri := norm_sub_le (-(Complex.I*(z-(x : ℂ)))) (complexSlope t w-modelDerivative t w)
    simp only [norm_neg,norm_mul,Complex.norm_I,one_mul] at htri
    have hcancel : 4*x*(1/x)/2=2 := by field_simp; ring
    rw [hcancel]
    linarith
  obtain ⟨v,hv,hroot⟩ := RiemannQuarticQuantitativeSaddle.scalar_ball_surj
    (complexSlope t) w A (1/x) (by positivity) hAn hd hb htarget
  refine ⟨v,⟨hv,hroot⟩,?_⟩
  intro z hz
  exact RiemannQuarticQuantitativeSaddle.scalar_ball_injective
    (complexSlope t) w A (1/x) hAn hd hb hz.1 hv (hz.2.trans hroot.symm)


theorem actual_far_saddle (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) :
    ∃! v, v ∈ closedBall w (1/x) ∧ complexSlope t v= -(Complex.I*(x : ℂ)) :=
  actual_far_frequency_disk t x ht hx w hr hi hp hs (x : ℂ) (by simp)

theorem corrected_saddle_geometry (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) (hv : v ∈ closedBall w (1/x)) :
    1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hpol : 4*t*‖w‖^3+9 ≤ x := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 3]
  have hdist : ‖v-w‖ ≤ 1/x := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hd2 : ‖v-w‖ ≤ 2/x := hdist.trans (by apply (div_le_div_iff_of_pos_right hx0).mpr; norm_num)
  have hdom := neighbor_domain t x ht (by linarith) w v (by linarith) hi hs hpol hd2
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

open Filter

theorem eventually_actual_far_saddle (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ a : ℝ in atTop, ∃ w v : ℂ,
      w ∈ closedBall (anchor a) (1/1024) ∧
      modelDerivative t w= -(Complex.I*((4*Real.pi*Real.exp (4*a) : ℝ) : ℂ)) ∧
      v ∈ closedBall w (1/(4*Real.pi*Real.exp (4*a))) ∧
      complexSlope t v= -(Complex.I*((4*Real.pi*Real.exp (4*a) : ℝ) : ℂ)) ∧
      1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 := by
  filter_upwards [eventually_concrete_far_saddle t (by linarith),
    RiemannQuarticDomain.quartic_exponent_dominated (80000*(t+1)) 0,
    eventually_ge_atTop (240040 : ℝ)] with a hex hdom ha
  obtain ⟨w,⟨hw,hs⟩,_⟩ := hex
  have ha0 : 0 ≤ a := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hp3 := pow_le_pow_left₀ (by linarith : 0 ≤ a+3) (by linarith : a+3 ≤ 2*a) 3
  have hp34 : a^3 ≤ a^4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ a-1) (pow_nonneg ha0 3)]
  have hM : (a+3)^3 ≤ 8*a^4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 10000*(t+1))
  simp only [zero_mul,add_zero] at hdom
  have hscale : 10000*(t+1)*(a+3)^3 ≤ 4*Real.pi*Real.exp (4*a) := by
    nlinarith [Real.pi_gt_three,Real.exp_pos (4*a)]
  have hM1 : 1 ≤ (a+3)^3 := one_le_pow₀ (by linarith)
  have hx : 10000 ≤ 4*Real.pi*Real.exp (4*a) := by
    nlinarith [mul_le_mul_of_nonneg_left hM1 (by positivity : 0 ≤ t+1)]
  have hd : ‖w-anchor a‖ ≤ (1/1024 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hreal := (Complex.abs_re_le_norm (w-anchor a)).trans hd
  have hbr : (anchor a).re=a := by simp [anchor]
  simp only [Complex.sub_re,hbr] at hreal
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hreal).1]
  have hnorm : ‖w‖+1 ≤ a+3 := by
    have hn := norm_add_le (w-anchor a) (anchor a)
    rw [sub_add_cancel] at hn
    have hb := anchor_norm a ha0
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖+1) hnorm 3
  have hps : 100*(t*(‖w‖+1)^3+1) ≤ 4*Real.pi*Real.exp (4*a) := by
    have hmul := mul_le_mul_of_nonneg_left hpow ht0
    nlinarith [pow_nonneg (by linarith : 0 ≤ a+3) 3]
  have hi := (far_saddle_geometry a (by linarith) w hw).2
  obtain ⟨v,⟨hv,hroot⟩,_⟩ := actual_far_saddle t _ ht hx w hr hi hps hs
  have hg := corrected_saddle_geometry t _ ht hx w v hr hi hps hs hv
  exact ⟨w,v,hw,hs,hv,hroot,hg⟩


theorem eventually_frequency_actual_saddle (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ x : ℝ in atTop, ∃ w v : ℂ,
      w ∈ closedBall (anchor (Real.log (x/(4*Real.pi))/4)) (1/1024) ∧
      modelDerivative t w= -(Complex.I*(x : ℂ)) ∧
      v ∈ closedBall w (1/x) ∧ complexSlope t v= -(Complex.I*(x : ℂ)) ∧
      1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 := by
  have hlin : Tendsto (fun x : ℝ => x/(4*Real.pi)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have hlog := Real.tendsto_log_atTop.comp hlin
  have hlim := hlog.atTop_div_const (by norm_num : (0 : ℝ)<4)
  filter_upwards [hlim.eventually (eventually_actual_far_saddle t ht),
    eventually_gt_atTop (0 : ℝ)] with x hex hx
  obtain ⟨w,v,hw,hs,hv,hroot,hg⟩ := hex
  have hid : 4*Real.pi*Real.exp (4*(Real.log (x/(4*Real.pi))/4))=x := by
    rw [show 4*(Real.log (x/(4*Real.pi))/4)=Real.log (x/(4*Real.pi)) by ring,
      Real.exp_log (by positivity : (0 : ℝ)<x/(4*Real.pi))]
    field_simp
  simp only [Function.comp_def] at hs hw hv hroot
  rw [hid] at hs hv hroot
  exact ⟨w,v,hw,hs,hv,hroot,hg⟩

theorem eventually_actual_saddle_contour (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ x : ℝ in atTop, ∃ v : ℂ,
      complexSlope t v= -(Complex.I*(x : ℂ)) ∧
      1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 ∧
      RiemannQuarticFlow.flow t (x : ℂ)=
        ((∫ s : ℝ in Ioi 0, RiemannQuarticFrequencyBranch.saddleWeight t (x : ℂ)
          ((s : ℂ)+(v.im : ℂ)*Complex.I))+
        (∫ s : ℝ in Ioi 0, RiemannQuarticFrequencyBranch.saddleWeight t (-(x : ℂ))
          ((s : ℂ)-(v.im : ℂ)*Complex.I)))/2 := by
  filter_upwards [eventually_frequency_actual_saddle t ht] with x hex
  obtain ⟨w,v,hw,hs,hv,hroot,hr,hi,hn⟩ := hex
  exact ⟨v,hroot,hr,hi,hn,RiemannQuarticNaturalContour.flow_eq_paired_horizontal t (x : ℂ) v.im hi⟩


theorem actual_far_deriv_norm_lower (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) (hv : v ∈ closedBall w (1/x)) :
    2*x ≤ ‖deriv (complexSlope t) v‖ := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hpol : 4*t*‖w‖^3+9 ≤ x := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 3]
  let A := -(4 : ℂ)*Complex.I*(x : ℂ)
  have hA : ‖A‖=4*x := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0,mul_one]
  have h1 := neighbor_error_deriv_bound t x ht (by linarith) w v (by linarith) hi hs hpol hv
  have h2 := model_deriv_near_far_saddle t x ht hx w v hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have hsmall := mul_le_mul_of_nonneg_right (small_error_at_large_real_part w.re hr) hx0.le
  have h3 := norm_add_le (deriv (complexSlope t) v-deriv (modelDerivative t) v)
    (deriv (modelDerivative t) v-A)
  rw [sub_add_sub_cancel] at h3
  change ‖deriv (modelDerivative t) v-A‖ ≤ x at h2
  have h4 := norm_sub_le (deriv (complexSlope t) v) (deriv (complexSlope t) v-A)
  rw [sub_sub_cancel,hA] at h4
  nlinarith

theorem actual_weight_critical (t : ℝ) (z v : ℂ)
    (hv : 0 < (Complex.exp (4*v)).re) (hk : kernelComplex v ≠ 0)
    (hs : complexSlope t v= -(Complex.I*z)) :
    HasDerivAt (RiemannQuarticFrequencyBranch.saddleWeight t z) 0 v ∧
      RiemannQuarticFrequencyBranch.saddleWeight t z v ≠ 0 := by
  have h := RiemannQuarticSpatialPhase.spatial_weight_hasDerivAt t z v hv hk
  simp only [hs,neg_add_cancel,zero_mul] at h
  exact ⟨h,mul_ne_zero (Complex.exp_ne_zero _) hk⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarCorrection
