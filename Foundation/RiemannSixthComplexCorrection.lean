import Foundation.RiemannSixthFarCorrection
import Foundation.RiemannEvenFarModelSaddle
import Foundation.RiemannEvenNaturalContour
import Foundation.RiemannEvenUniformFarScale
import Foundation.RiemannSixthFarConstruction
/-! Actual A6 logarithmic saddles at lower-half-plane complex frequencies.
Genuine arithmetic domains and inverse bounds precede contour or dominance claims. -/
noncomputable section
open Set Metric Complex Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthComplexCorrection
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannThetaComplexKernel
open RiemannQuarticFarCorrection (neighbor_real_margin exp4_difference_bound small_error_at_large_real_part)

theorem model_exp_norm_le_frequency (t : ℝ) (z : ℂ) (ht : 0 ≤ t) (hx : 0 < ‖z‖) (w : ℂ)
    (hpoly : 6*t*‖w‖^5+9 ≤ ‖z‖) (hs : modelDerivative 3 t w= -(Complex.I*z)) :
    ‖Complex.exp (4*w)‖ ≤ ‖z‖ := by
  have he : 4*(Real.pi : ℂ)*Complex.exp (4*w)=6*(t : ℂ)*w^5+9+Complex.I*z := by
    unfold modelDerivative at hs
    linear_combination -hs
  have hn := congrArg norm he
  have h1 := norm_add_le (6*(t : ℂ)*w^5+9) (Complex.I*z)
  have h2 := norm_add_le (6*(t : ℂ)*w^5) (9 : ℂ)
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht,abs_of_pos Real.pi_pos,Complex.norm_I,one_mul] at hn h1 h2
  nlinarith [norm_nonneg (Complex.exp (4*w)),Real.pi_gt_three]


theorem neighbor_domain (t : ℝ) (z : ℂ) (hz : z.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖z‖) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*z))
    (hp : 6*t*‖w‖^5+9 ≤ ‖z‖) (hv : ‖v-w‖ ≤ 2/‖z‖) :
    0 ≤ v.re ∧ 1 ≤ (Complex.exp (4*v)).re ∧
      (t*w.re^5-z.im)/32 ≤ (Complex.exp (4*v)).re := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < ‖z‖ := by linarith
  have hE := model_exp_norm_le_frequency t z ht0 hx0 w hp hs
  have hn := neighbor_real_margin ‖z‖ hx w v hE hv
  have hlow := RiemannSixthSaddleTheta.model_real_margin t z w ht0 (by linarith) hi hs
  have htr0 : 0 ≤ t*w.re^5 := by positivity
  have hR0 : 0 ≤ (Complex.exp (4*w)).re := by nlinarith [Real.pi_pos]
  have hp4 := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hR0
  have hcub : 32768 ≤ w.re^5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤32) hr 5
    norm_num at h
    linarith
  have htcub : w.re^5 ≤ t*w.re^5 := by nlinarith
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
    (hs : modelDerivative 3 t w= -(Complex.I*z))
    (hp : 6*t*‖w‖^5+9 ≤ ‖z‖) (hv : ‖v-w‖ ≤ 2/‖z‖) :
    ‖complexSlope 3 t v-modelDerivative 3 t v‖ ≤ 30005*Real.exp (-w.re) := by
  have hdom := neighbor_domain t z hz ht hx w v hr hi hs hp hv
  have hd : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ (by linarith : 0 < ‖z‖)).mpr (by linarith))
  have hcoord := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hcoord
  have hlo := (abs_le.mp hcoord).1
  have hhi := (abs_le.mp hcoord).2
  have heq : complexSlope 3 t v-modelDerivative 3 t v=
      kernelDerivative v/kernelComplex v-(9-4*(Real.pi : ℂ)*Complex.exp (4*v)) := by
    unfold complexSlope modelDerivative
    rw [(kernelComplex_hasDerivAt v (by linarith [hdom.2.1])).deriv]
    ring
  rw [heq]
  apply (RiemannQuarticSaddleNeighborhood.logDerivative_coarse_bound v hdom.1 hdom.2.1).trans
  have hcub : 1024*w.re ≤ w.re^5 := by
    have hsq : 1024 ≤ w.re^4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hr 4
      norm_num at hh
      linarith
    have h := mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)
    nlinarith
  have htcub : w.re^5 ≤ t*w.re^5 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 3]
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
    (hs : modelDerivative 3 t w= -(Complex.I*z))
    (hp : 6*t*‖w‖^5+9 ≤ ‖z‖) :
    AnalyticOnNhd ℂ (complexSlope 3 t) (closedBall w (2/‖z‖)) := by
  intro v hv
  have hd : ‖v-w‖ ≤ 2/‖z‖ := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hdom := neighbor_domain t z hz ht hx w v hr hi hs hp hd
  have ha := kernelComplex_analyticAt v (by linarith [hdom.2.1])
  have hn := kernel_ne_zero v hdom.1 hdom.2.1
  exact (analyticAt_const.mul (analyticAt_id.pow 5)).add (ha.deriv.div ha hn)


theorem neighbor_error_deriv_bound (t : ℝ) (z : ℂ) (hz : z.im ≤ 0) (ht : 1 ≤ t) (hx : 8 ≤ ‖z‖) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*z))
    (hp : 6*t*‖w‖^5+9 ≤ ‖z‖) (hv : v ∈ closedBall w (1/‖z‖)) :
    ‖deriv (complexSlope 3 t) v-deriv (modelDerivative 3 t) v‖ ≤
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
  have hm : AnalyticOnNhd ℂ (modelDerivative 3 t) (closedBall w (2/‖z‖)) := by
    intro z _
    unfold modelDerivative
    fun_prop
  have hd := ((ha.sub hm).mono hsub).differentiableOn.diffContOnCl_ball (Subset.refl _)
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by positivity : (0 : ℝ)<1/‖z‖) hd (fun u hu => neighbor_error_bound t z hz ht hx w u hr hi hs hp
      (by simpa only [mem_closedBall,dist_eq_norm] using hsub (sphere_subset_closedBall hu)))
  have hvin : v ∈ closedBall w (2/‖z‖) := hsub (mem_closedBall_self (by positivity))
  rw [deriv_sub (ha v hvin).differentiableAt (modelDerivative_hasDerivAt 3 t v).differentiableAt] at h
  simpa only [one_div,div_inv_eq_mul] using h



theorem model_deriv_near_far_saddle (t : ℝ) (z : ℂ) (ht : 1 ≤ t) (hx : 10000 ≤ ‖z‖) (w v : ℂ)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ ‖z‖)
    (hs : modelDerivative 3 t w= -(Complex.I*z)) (hv : ‖v-w‖ ≤ 1/‖z‖) :
    ‖deriv (modelDerivative 3 t) v-(-(4 : ℂ)*Complex.I*z)‖ ≤ ‖z‖ := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < ‖z‖ := by linarith
  let M := ‖w‖+1
  have hM : 1 ≤ M := by dsimp [M]; linarith [norm_nonneg w]
  have hM0 : 0 ≤ M := by linarith
  have hM23 : M^4 ≤ M^5 := pow_le_pow_right₀ hM (by norm_num)
  have hwM : ‖w‖ ≤ M := by dsimp [M]; linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) hwM 5
  have hpol : 6*t*‖w‖^5+9 ≤ ‖z‖ := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    change 10000*(t*M^5+1) ≤ ‖z‖ at hp
    nlinarith [pow_nonneg hM0 5]
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
  have heq : 4*(Real.pi : ℂ)*Complex.exp (4*w)=6*(t : ℂ)*w^5+9+Complex.I*z := by
    unfold modelDerivative at hs
    linear_combination -hs
  have hid : deriv (modelDerivative 3 t) v-(-(4 : ℂ)*Complex.I*z)=
      (30*(t : ℂ)*v^4-24*(t : ℂ)*w^5-36)-
        16*(Real.pi : ℂ)*(Complex.exp (4*v)-Complex.exp (4*w)) := by
    rw [(modelDerivative_hasDerivAt 3 t v).deriv]
    linear_combination -4*heq
  rw [hid]
  have h1 := norm_sub_le (30*(t : ℂ)*v^4-24*(t : ℂ)*w^5-36)
    (16*(Real.pi : ℂ)*(Complex.exp (4*v)-Complex.exp (4*w)))
  have h2 := norm_sub_le (30*(t : ℂ)*v^4-24*(t : ℂ)*w^5) (36 : ℂ)
  have h3 := norm_sub_le (30*(t : ℂ)*v^4) (24*(t : ℂ)*w^5)
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht0,abs_of_pos Real.pi_pos] at h1 h2 h3
  have hvpow := pow_le_pow_left₀ (norm_nonneg v) hvM 4
  have hvm := mul_le_mul_of_nonneg_left (hvpow.trans hM23) ht0
  have hwm := mul_le_mul_of_nonneg_left hpw ht0
  have hpie := mul_le_mul Real.pi_lt_four.le he8 (norm_nonneg _) (by norm_num : (0 : ℝ)≤4)
  change 10000*(t*M^5+1) ≤ ‖z‖ at hp
  nlinarith



theorem actual_far_frequency_disk (t : ℝ) (z : ℂ) (hz : z.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖z‖) (w : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ ‖z‖)
    (hs : modelDerivative 3 t w= -(Complex.I*z))
    (q : ℂ) (hq : ‖q-z‖ ≤ 1) :
    ∃! v, v ∈ closedBall w (1/‖z‖) ∧ complexSlope 3 t v= -(Complex.I*q) := by
  have hx0 : 0 < ‖z‖ := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hpol : 6*t*‖w‖^5+9 ≤ ‖z‖ := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 5]
  have hsmall := small_error_at_large_real_part w.re hr
  have ha := neighbor_slope_analytic t z hz ht (by linarith) w (by linarith) hi hs hpol
  let A := -(4 : ℂ)*Complex.I*z
  have hA : ‖A‖=4*‖z‖ := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,mul_one]
  have hAn : A ≠ 0 := norm_pos_iff.mp (by rw [hA]; positivity)
  have hsub : closedBall w (1/‖z‖) ⊆ closedBall w (2/‖z‖) :=
    closedBall_subset_closedBall (by apply (div_le_div_iff_of_pos_right hx0).mpr; norm_num)
  have hd : ∀ v ∈ closedBall w (1/‖z‖), DifferentiableAt ℂ (complexSlope 3 t) v :=
    fun v hv => (ha v (hsub hv)).differentiableAt
  have hb : ∀ v ∈ closedBall w (1/‖z‖), ‖deriv (complexSlope 3 t) v-A‖ ≤ ‖A‖/2 := by
    intro v hv
    have h1 := neighbor_error_deriv_bound t z hz ht (by linarith) w v (by linarith) hi hs hpol hv
    have h2 := model_deriv_near_far_saddle t z ht hx w v hp hs
      (by simpa only [mem_closedBall,dist_eq_norm] using hv)
    have h3 := norm_add_le (deriv (complexSlope 3 t) v-deriv (modelDerivative 3 t) v)
      (deriv (modelDerivative 3 t) v-A)
    rw [sub_add_sub_cancel] at h3
    have hm := mul_le_mul_of_nonneg_right hsmall hx0.le
    rw [hA]
    change ‖deriv (modelDerivative 3 t) v-A‖ ≤ ‖z‖ at h2
    nlinarith
  have hres := neighbor_error_bound t z hz ht (by linarith) w w (by linarith) hi hs hpol
    (by simp; positivity)
  have htarget : -(Complex.I*q) ∈ closedBall (complexSlope 3 t w) (‖A‖*(1/‖z‖)/2) := by
    rw [mem_closedBall,dist_eq_norm,hA]
    have hid : -(Complex.I*q)-complexSlope 3 t w=
        -(Complex.I*(q-z))-(complexSlope 3 t w-modelDerivative 3 t w) := by rw [hs]; ring
    rw [hid]
    have htri := norm_sub_le (-(Complex.I*(q-z))) (complexSlope 3 t w-modelDerivative 3 t w)
    simp only [norm_neg,norm_mul,Complex.norm_I,one_mul] at htri
    have hcancel : 4*‖z‖*(1/‖z‖)/2=2 := by field_simp; ring
    rw [hcancel]
    linarith
  obtain ⟨v,hv,hroot⟩ := RiemannQuarticQuantitativeSaddle.scalar_ball_surj
    (complexSlope 3 t) w A (1/‖z‖) (by positivity) hAn hd hb htarget
  refine ⟨v,⟨hv,hroot⟩,?_⟩
  intro q hz
  exact RiemannQuarticQuantitativeSaddle.scalar_ball_injective
    (complexSlope 3 t) w A (1/‖z‖) hAn hd hb hz.1 hv (hz.2.trans hroot.symm)



theorem actual_far_saddle (t : ℝ) (z : ℂ) (hz : z.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖z‖) (w : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ ‖z‖)
    (hs : modelDerivative 3 t w= -(Complex.I*z)) :
    ∃! v, v ∈ closedBall w (1/‖z‖) ∧ complexSlope 3 t v= -(Complex.I*z) :=
  actual_far_frequency_disk t z hz ht hx w hr hi hp hs z (by simp)


theorem corrected_saddle_geometry (t : ℝ) (z : ℂ) (hz : z.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖z‖) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ ‖z‖)
    (hs : modelDerivative 3 t w= -(Complex.I*z)) (hv : v ∈ closedBall w (1/‖z‖)) :
    1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 := by
  have hx0 : 0 < ‖z‖ := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hpol : 6*t*‖w‖^5+9 ≤ ‖z‖ := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 5]
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
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ ‖z‖)
    (hs : modelDerivative 3 t w= -(Complex.I*z)) (hv : v ∈ closedBall w (1/‖z‖)) :
    2*‖z‖ ≤ ‖deriv (complexSlope 3 t) v‖ := by
  have hx0 : 0 < ‖z‖ := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hpol : 6*t*‖w‖^5+9 ≤ ‖z‖ := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 5]
  let A := -(4 : ℂ)*Complex.I*z
  have hA : ‖A‖=4*‖z‖ := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,mul_one]
  have h1 := neighbor_error_deriv_bound t z hz ht (by linarith) w v (by linarith) hi hs hpol hv
  have h2 := model_deriv_near_far_saddle t z ht hx w v hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have hsmall := mul_le_mul_of_nonneg_right (small_error_at_large_real_part w.re hr) hx0.le
  have h3 := norm_add_le (deriv (complexSlope 3 t) v-deriv (modelDerivative 3 t) v)
    (deriv (modelDerivative 3 t) v-A)
  rw [sub_add_sub_cancel] at h3
  change ‖deriv (modelDerivative 3 t) v-A‖ ≤ ‖z‖ at h2
  have h4 := norm_sub_le (deriv (complexSlope 3 t) v) (deriv (complexSlope 3 t) v-A)
  rw [sub_sub_cancel,hA] at h4
  nlinarith


theorem exists_uniform_actual_far_complex_disks :
    ∃ K : ℝ, 0 < K ∧ ∀ t u : ℝ, 1 ≤ t → 120021 ≤ u →
      RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      ∀ z : ℂ, z.im ≤ 0 → K*RiemannQuarticTransitionSaddle.realScale u ≤ ‖z‖ →
        ∃ w : ℂ, 10000 ≤ ‖z‖ ∧ 120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
          10000*(t*(‖w‖+1)^5+1) ≤ ‖z‖ ∧ modelDerivative 3 t w = -(Complex.I*z) ∧
          ∀ q : ℂ, ‖q-z‖ ≤ 1 →
            ∃! v, v ∈ closedBall w (1/‖z‖) ∧ complexSlope 3 t v = -(Complex.I*q) := by
  obtain ⟨D,hD,hscale⟩ := RiemannEvenUniformFarScale.exists_uniform_stationary_far_scale 3 (by norm_num)
  refine ⟨Real.exp (4*D),Real.exp_pos _,?_⟩
  intro t u ht hu hstat z hz hcut
  obtain ⟨a,ha,hn⟩ := RiemannEvenUniformFarScale.far_parameter u D ‖z‖ hcut
  have hsc := hscale t u a ht (by norm_num; linarith) hstat ha
  norm_num at hsc
  change 490000*(t+1)*(a+4)^5 ≤ 4*Real.pi*Real.exp (4*a) at hsc
  have ha' : 120021 ≤ a := by linarith
  have hpoly : 490000*(t+1)*(a+2)^5 ≤ 4*Real.pi*Real.exp (4*a) := by
    have hp := pow_le_pow_left₀ (by linarith : 0 ≤ a+2) (by linarith : a+2 ≤ a+4) 5
    exact (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 490000*(t+1))).trans hsc
  change ‖z‖ = 4*Real.pi*Real.exp (4*a) at hn
  obtain ⟨w,⟨hw,hroot⟩,hunique⟩ := RiemannEvenFarModelSaddle.lower_half_circle_saddle 3 (by norm_num)
    t a (by linarith) (by linarith) (by norm_num; exact hpoly) z hz hn
  have hg := RiemannQuarticComplexModelSaddle.complexAnchor_geometry a (by linarith) z hz hn
  have hd : ‖w-RiemannQuarticComplexModelSaddle.complexAnchor z‖ ≤ (1/1024 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hw
  have hreal := (Complex.abs_re_le_norm (w-RiemannQuarticComplexModelSaddle.complexAnchor z)).trans hd
  simp only [Complex.sub_re,hg.1] at hreal
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hreal).1]
  have hnorm : ‖w‖+1 ≤ a+3 := by
    have hb := norm_add_le (w-RiemannQuarticComplexModelSaddle.complexAnchor z)
      (RiemannQuarticComplexModelSaddle.complexAnchor z)
    rw [sub_add_cancel] at hb
    linarith [hg.2.2]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖+1) (hnorm.trans (by linarith : a+3 ≤ a+4)) 5
  have hps : 10000*(t*(‖w‖+1)^5+1) ≤ ‖z‖ := by
    have hm := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ t)
    have h1 : 1 ≤ (a+4)^5 := one_le_pow₀ (by linarith : 1 ≤ a+4)
    rw [← hn] at hsc
    nlinarith [pow_nonneg (by linarith : 0 ≤ a+4) 5]
  have hi : |w.im| ≤ 1/2 := by
    have hh := abs_add_le (w.im-(RiemannQuarticComplexModelSaddle.complexAnchor z).im)
      (RiemannQuarticComplexModelSaddle.complexAnchor z).im
    rw [sub_add_cancel] at hh
    have hdiff := (Complex.abs_im_le_norm (w-RiemannQuarticComplexModelSaddle.complexAnchor z)).trans hd
    simp only [Complex.sub_im] at hdiff
    linarith [hg.2.1,Real.pi_lt_d2]
  have hx : 10000 ≤ ‖z‖ := by
    have hp0 : 0 ≤ t*(‖w‖+1)^5 := by positivity
    nlinarith
  exact ⟨w,hx,hr,hi,hps,hroot,fun q hq => actual_far_frequency_disk t z hz ht hx w hr hi hps hroot q hq⟩

theorem exists_uniform_actual_far_lower_halfplane :
    ∃ K : ℝ, 0 < K ∧ ∀ t u : ℝ, 1 ≤ t → 120021 ≤ u →
      RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      ∀ z : ℂ, z.im ≤ 0 → K*RiemannQuarticTransitionSaddle.realScale u ≤ ‖z‖ →
        ∃ v : ℂ, complexSlope 3 t v = -(Complex.I*z) ∧
          1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 ∧
          1 ≤ (Complex.exp (4*v)).re ∧ 2*‖z‖ ≤ ‖deriv (complexSlope 3 t) v‖ ∧
          HasDerivAt (RiemannEvenComplexWeight.weight 3 t z) 0 v ∧
          RiemannEvenComplexWeight.weight 3 t z v ≠ 0 ∧
          MeasureTheory.IntegrableOn (fun s : ℝ => RiemannEvenComplexWeight.weight 3 t z
            ((s : ℂ)+(v.im : ℂ)*Complex.I)) (Ioi 0) ∧
          MeasureTheory.IntegrableOn (fun s : ℝ => RiemannEvenComplexWeight.weight 3 t (-z)
            ((s : ℂ)-(v.im : ℂ)*Complex.I)) (Ioi 0) ∧
          RiemannEvenFlow.flow 3 t z =
            ((∫ s : ℝ in Ioi 0, RiemannEvenComplexWeight.weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))+
              (∫ s : ℝ in Ioi 0, RiemannEvenComplexWeight.weight 3 t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)))/2 := by
  obtain ⟨K,hK,hC⟩ := exists_uniform_actual_far_complex_disks
  refine ⟨K,hK,?_⟩
  intro t u ht hu hstat z hz hcut
  obtain ⟨w,hx,hr,hi,hp,hs,hroots⟩ := hC t u ht hu hstat z hz hcut
  obtain ⟨v,⟨hv,hroot⟩,hunique⟩ := hroots z (by simp)
  have hgeom := corrected_saddle_geometry t z hz ht hx w v hr hi hp hs hv
  have hderiv := actual_far_deriv_norm_lower t z hz ht hx w v hr hi hp hs hv
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hpol : 6*t*‖w‖^5+9 ≤ ‖z‖ := by
    have hm := mul_le_mul_of_nonneg_left hpw (by linarith : 0 ≤ t)
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 5]
  have hv2 : ‖v-w‖ ≤ 2/‖z‖ := by
    have hd : ‖v-w‖ ≤ 1/‖z‖ := by simpa only [mem_closedBall,dist_eq_norm] using hv
    exact hd.trans ((div_le_div_iff_of_pos_right (by linarith : 0 < ‖z‖)).mpr (by norm_num))
  have hdom := neighbor_domain t z hz ht (by linarith) w v (by linarith) hi hs hpol hv2
  have hc := RiemannSixthFarConstruction.actual_weight_critical t z v (by linarith [hdom.2.1]) hgeom.2.2 hroot
  refine ⟨v,hroot,hgeom.1,hgeom.2.1,hgeom.2.2,hdom.2.1,hderiv,hc.1,hc.2,
    RiemannEvenNaturalContour.shifted_weight_integrable 3 t z v.im hgeom.2.1,?_,
    RiemannEvenNaturalContour.flow_eq_paired_horizontal 3 t z v.im hgeom.2.1⟩
  simpa only [Complex.ofReal_neg,neg_mul,← sub_eq_add_neg] using
    RiemannEvenNaturalContour.shifted_weight_integrable 3 t (-z) (-v.im) (by simpa only [abs_neg] using hgeom.2.1)

end OperatorDerivativeRewrite.Foundation.RiemannSixthComplexCorrection
