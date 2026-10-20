import Foundation.RiemannSixthSaddleTheta
import Foundation.RiemannQuarticFarCorrection

/-! Actual sixth-order far saddles on shrinking arithmetic domains. The
leading-model root is corrected; contour integration remains separate. -/
noncomputable section
open Set Metric Complex
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarCorrection
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannSixthSaddleTheta
open RiemannThetaComplexKernel

theorem model_exp_norm_bound (t x : ℝ) (ht : 0 ≤ t) (hx : 0 < x) (w : ℂ)
    (hp : 6*t*‖w‖^5+9 ≤ x) (hs : modelDerivative 3 t w = -(Complex.I*(x : ℂ))) :
    ‖Complex.exp (4*w)‖ ≤ x := by
  have he : 4*(Real.pi : ℂ)*Complex.exp (4*w) = 6*(t : ℂ)*w^5+9+Complex.I*(x : ℂ) := by
    norm_num [modelDerivative] at hs
    linear_combination -hs
  have hn := congrArg norm he
  have h1 := norm_add_le (6*(t : ℂ)*w^5+9) (Complex.I*(x : ℂ))
  have h2 := norm_add_le (6*(t : ℂ)*w^5) (9 : ℂ)
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht,abs_of_pos hx,abs_of_pos Real.pi_pos,Complex.norm_I,one_mul] at hn h1 h2
  nlinarith [norm_nonneg (Complex.exp (4*w)),Real.pi_gt_three]

theorem neighbor_domain (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w = -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 2/x) :
    0 ≤ v.re ∧ 1 ≤ (Complex.exp (4*v)).re ∧ t*w.re^5/32 ≤ (Complex.exp (4*v)).re := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  have hE := model_exp_norm_bound t x ht0 hx0 w hp hs
  have hn := RiemannQuarticFarCorrection.neighbor_real_margin x hx w v hE hv
  have hm := model_real_margin t (x : ℂ) w ht0 (by linarith) hi hs
  simp only [Complex.ofReal_im,sub_zero] at hm
  have ht5 : 0 ≤ t*w.re^5 := by positivity
  have hR0 : 0 ≤ (Complex.exp (4*w)).re := by nlinarith [Real.pi_pos]
  have hp4 := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hR0
  have hr5 : (32768 : ℝ) ≤ w.re^5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hr 5
    norm_num at h
    linarith
  have htr : w.re^5 ≤ t*w.re^5 := by nlinarith
  have hd : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hcoord := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hcoord
  refine ⟨?_,?_,?_⟩
  · linarith [(abs_le.mp hcoord).1]
  · nlinarith
  · nlinarith

theorem neighbor_error_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w = -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 2/x) :
    ‖complexSlope 3 t v-modelDerivative 3 t v‖ ≤ 30005*Real.exp (-w.re) := by
  have hdom := neighbor_domain t x ht hx w v hr hi hs hp hv
  have hd : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ (by linarith : 0 < x)).mpr (by linarith))
  have hcoord := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hcoord
  have hlo := (abs_le.mp hcoord).1
  have hhi := (abs_le.mp hcoord).2
  have hid : complexSlope 3 t v-modelDerivative 3 t v =
      kernelDerivative v/kernelComplex v-(9-4*(Real.pi : ℂ)*Complex.exp (4*v)) := by
    unfold complexSlope modelDerivative
    rw [(kernelComplex_hasDerivAt v (by linarith [hdom.2.1])).deriv]
    ring
  rw [hid]
  apply (RiemannQuarticSaddleNeighborhood.logDerivative_coarse_bound v hdom.1 hdom.2.1).trans
  have hcub : 1024*w.re ≤ w.re^3 := by
    have hsq : 1024 ≤ w.re^2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)
    nlinarith
  have h35 : w.re^3 ≤ w.re^5 := pow_le_pow_right₀ (by linarith : 1 ≤ w.re) (by norm_num)
  have htr : w.re^5 ≤ t*w.re^5 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 5]
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
    (by linarith [hdom.2.1] : 0 ≤ (Complex.exp (4*v)).re)
  have h1 : Real.exp (-4*v.re) ≤ Real.exp (-w.re) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (4*v.re)*Real.exp (-3*Real.pi*(Complex.exp (4*v)).re) ≤ Real.exp (-w.re) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hdom.2.2]
  have hh1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 5)
  have hh2 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 30000)
  nlinarith

theorem neighbor_slope_analytic (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w = -(Complex.I*(x : ℂ))) (hp : 6*t*‖w‖^5+9 ≤ x) :
    AnalyticOnNhd ℂ (complexSlope 3 t) (closedBall w (2/x)) := by
  intro v hv
  have hd : ‖v-w‖ ≤ 2/x := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hdom := neighbor_domain t x ht hx w v hr hi hs hp hd
  have ha := kernelComplex_analyticAt v (by linarith [hdom.2.1])
  have hn := RiemannThetaComplexKernel.kernel_ne_zero v hdom.1 hdom.2.1
  exact (analyticAt_const.mul (analyticAt_id.pow 5)).add (ha.deriv.div ha hn)

theorem neighbor_error_deriv_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w = -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : v ∈ closedBall w (1/x)) :
    ‖deriv (complexSlope 3 t) v-deriv (modelDerivative 3 t) v‖ ≤
      (30005*Real.exp (-w.re))*x := by
  have hx0 : 0 < x := by linarith
  have hsub : closedBall v (1/x) ⊆ closedBall w (2/x) := by
    intro z hz
    have h := dist_triangle z v w
    have hz' := mem_closedBall.mp hz
    have hv' := mem_closedBall.mp hv
    apply mem_closedBall.mpr
    have htwo : 1/x+1/x = 2/x := by ring
    linarith
  have ha := neighbor_slope_analytic t x ht hx w hr hi hs hp
  have hm : AnalyticOnNhd ℂ (modelDerivative 3 t) (closedBall w (2/x)) := by
    intro z _
    unfold modelDerivative
    fun_prop
  have hd := ((ha.sub hm).mono hsub).differentiableOn.diffContOnCl_ball (Subset.refl _)
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : (0 : ℝ) < 1/x) hd
    (fun z hz => neighbor_error_bound t x ht hx w z hr hi hs hp
      (by simpa only [mem_closedBall,dist_eq_norm] using hsub (sphere_subset_closedBall hz)))
  have hvin : v ∈ closedBall w (2/x) := hsub (mem_closedBall_self (by positivity))
  rw [deriv_sub (ha v hvin).differentiableAt (modelDerivative_hasDerivAt 3 t v).differentiableAt] at h
  simpa only [one_div,div_inv_eq_mul] using h

theorem model_deriv_near_far_saddle (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w v : ℂ)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
    (hs : modelDerivative 3 t w = -(Complex.I*(x : ℂ))) (hv : ‖v-w‖ ≤ 1/x) :
    ‖deriv (modelDerivative 3 t) v-(-(4 : ℂ)*Complex.I*(x : ℂ))‖ ≤ x := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  let M : ℝ := ‖w‖+1
  have hM : 1 ≤ M := by dsimp [M]; linarith [norm_nonneg w]
  have hw5 : ‖w‖^5 ≤ M^5 := pow_le_pow_left₀ (norm_nonneg w) (by dsimp [M]; linarith) 5
  have hv1 : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hvM : ‖v‖ ≤ M := by
    have h := norm_add_le (v-w) w
    rw [sub_add_cancel] at h
    dsimp [M]
    linarith
  have hv4 : ‖v‖^4 ≤ M^5 :=
    (pow_le_pow_left₀ (norm_nonneg v) hvM 4).trans (pow_le_pow_right₀ hM (by norm_num))
  have hpoly : 6*t*‖w‖^5+9 ≤ x := by
    have h := mul_le_mul_of_nonneg_left hw5 ht0
    have hpos : 0 ≤ t*M^5 := by positivity
    change 10000*(t*M^5+1) ≤ x at hp
    nlinarith
  have hE := model_exp_norm_bound t x ht0 hx0 w hpoly hs
  have hdiff := RiemannQuarticFarCorrection.exp4_difference_bound w v (by
    have hfrac : 1/x ≤ (1/4 : ℝ) := (div_le_iff₀ hx0).mpr (by linarith)
    linarith)
  have hsmall : ‖Complex.exp (4*v)-Complex.exp (4*w)‖ ≤ 8 := by
    have h := mul_le_mul hE hv (norm_nonneg _) hx0.le
    have hc : x*(1/x) = 1 := by field_simp
    rw [hc] at h
    nlinarith
  have hlarge : ‖16*(Real.pi : ℂ)*(Complex.exp (4*v)-Complex.exp (4*w))‖ ≤ 512 := by
    rw [norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    have h := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 16*Real.pi by positivity)
    nlinarith [Real.pi_lt_four]
  have hid : deriv (modelDerivative 3 t) v-(-(4 : ℂ)*Complex.I*(x : ℂ)) =
      30*(t : ℂ)*v^4-24*(t : ℂ)*w^5-36-
        16*(Real.pi : ℂ)*(Complex.exp (4*v)-Complex.exp (4*w)) := by
    rw [(modelDerivative_hasDerivAt 3 t v).deriv]
    norm_num [modelDerivative] at hs ⊢
    linear_combination 4*hs
  rw [hid]
  have hn1 := norm_sub_le (30*(t : ℂ)*v^4-24*(t : ℂ)*w^5-36)
    (16*(Real.pi : ℂ)*(Complex.exp (4*v)-Complex.exp (4*w)))
  have hn2 := norm_sub_le (30*(t : ℂ)*v^4-24*(t : ℂ)*w^5) (36 : ℂ)
  have hn3 := norm_sub_le (30*(t : ℂ)*v^4) (24*(t : ℂ)*w^5)
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0] at hn2 hn3
  have htv := mul_le_mul_of_nonneg_left hv4 ht0
  have htw := mul_le_mul_of_nonneg_left hw5 ht0
  change 10000*(t*M^5+1) ≤ x at hp
  nlinarith

theorem actual_far_frequency_disk (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
    (hs : modelDerivative 3 t w = -(Complex.I*(x : ℂ)))
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    ∃! v, v ∈ closedBall w (1/x) ∧ complexSlope 3 t v = -(Complex.I*z) := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hpol : 6*t*‖w‖^5+9 ≤ x := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 5]
  have hsmall := RiemannQuarticFarCorrection.small_error_at_large_real_part w.re hr
  have ha := neighbor_slope_analytic t x ht (by linarith) w (by linarith) hi hs hpol
  let A : ℂ := -(4 : ℂ)*Complex.I*(x : ℂ)
  have hA : ‖A‖ = 4*x := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0,mul_one]
  have hAn : A ≠ 0 := norm_pos_iff.mp (by rw [hA]; positivity)
  have hsub : closedBall w (1/x) ⊆ closedBall w (2/x) :=
    closedBall_subset_closedBall (by apply (div_le_div_iff_of_pos_right hx0).mpr; norm_num)
  have hd : ∀ v ∈ closedBall w (1/x), DifferentiableAt ℂ (complexSlope 3 t) v :=
    fun v hv => (ha v (hsub hv)).differentiableAt
  have hb : ∀ v ∈ closedBall w (1/x), ‖deriv (complexSlope 3 t) v-A‖ ≤ ‖A‖/2 := by
    intro v hv
    have h1 := neighbor_error_deriv_bound t x ht (by linarith) w v (by linarith) hi hs hpol hv
    have h2 := model_deriv_near_far_saddle t x ht hx w v hp hs
      (by simpa only [mem_closedBall,dist_eq_norm] using hv)
    have h3 := norm_add_le (deriv (complexSlope 3 t) v-deriv (modelDerivative 3 t) v)
      (deriv (modelDerivative 3 t) v-A)
    rw [sub_add_sub_cancel] at h3
    have hm := mul_le_mul_of_nonneg_right hsmall hx0.le
    rw [hA]
    change ‖deriv (modelDerivative 3 t) v-A‖ ≤ x at h2
    nlinarith
  have hres := neighbor_error_bound t x ht (by linarith) w w (by linarith) hi hs hpol (by simp; positivity)
  have htarget : -(Complex.I*z) ∈ closedBall (complexSlope 3 t w) (‖A‖*(1/x)/2) := by
    rw [mem_closedBall,dist_eq_norm,hA]
    have hid : -(Complex.I*z)-complexSlope 3 t w =
        -(Complex.I*(z-(x : ℂ)))-(complexSlope 3 t w-modelDerivative 3 t w) := by rw [hs]; ring
    rw [hid]
    have htri := norm_sub_le (-(Complex.I*(z-(x : ℂ)))) (complexSlope 3 t w-modelDerivative 3 t w)
    simp only [norm_neg,norm_mul,Complex.norm_I,one_mul] at htri
    have hc : 4*x*(1/x)/2 = 2 := by field_simp; ring
    rw [hc]
    linarith
  obtain ⟨v,hv,hroot⟩ := RiemannQuarticQuantitativeSaddle.scalar_ball_surj
    (complexSlope 3 t) w A (1/x) (by positivity) hAn hd hb htarget
  refine ⟨v,⟨hv,hroot⟩,?_⟩
  intro q hq
  exact RiemannQuarticQuantitativeSaddle.scalar_ball_injective
    (complexSlope 3 t) w A (1/x) hAn hd hb hq.1 hv (hq.2.trans hroot.symm)

theorem actual_far_saddle (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
    (hs : modelDerivative 3 t w = -(Complex.I*(x : ℂ))) :
    ∃! v, v ∈ closedBall w (1/x) ∧ complexSlope 3 t v = -(Complex.I*(x : ℂ)) :=
  actual_far_frequency_disk t x ht hx w hr hi hp hs (x : ℂ) (by simp)

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarCorrection
