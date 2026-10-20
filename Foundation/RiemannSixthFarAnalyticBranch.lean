import Foundation.RiemannSixthFarCorrection

/-! Coherent holomorphic actual A6 saddles on a unit frequency disk.
The selection is controlled quantitatively and remains in the theta strip. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarAnalyticBranch
open RiemannSixthFarCorrection RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannThetaComplexKernel
open RiemannQuarticQuantitativeSaddle

private theorem polynomial_bound (t x : ℝ) (ht : 1 ≤ t) (w : ℂ)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) : 6*t*‖w‖^5+9 ≤ x := by
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hm := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ t)
  nlinarith [pow_nonneg (norm_nonneg w) 5]

variable (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
  (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
  (hs : modelDerivative 3 t w = -(Complex.I*(x : ℂ)))
include ht hx hr hi hp hs

theorem derivative_affine_bound (v : ℂ) (hv : v ∈ closedBall w (1/x)) :
    ‖deriv (complexSlope 3 t) v-(-(4 : ℂ)*Complex.I*(x : ℂ))‖ ≤ 2*x := by
  have hpol := polynomial_bound t x ht w hp
  have h1 := neighbor_error_deriv_bound t x ht (by linarith) w v (by linarith) hi hs hpol hv
  have h2 := model_deriv_near_far_saddle t x ht hx w v hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have h3 := norm_add_le (deriv (complexSlope 3 t) v-deriv (modelDerivative 3 t) v)
    (deriv (modelDerivative 3 t) v-(-(4 : ℂ)*Complex.I*(x : ℂ)))
  rw [sub_add_sub_cancel] at h3
  have hm := mul_le_mul_of_nonneg_right
    (RiemannQuarticFarCorrection.small_error_at_large_real_part w.re hr) (by linarith : 0 ≤ x)
  linarith

theorem derivative_norm_lower (v : ℂ) (hv : v ∈ closedBall w (1/x)) :
    2*x ≤ ‖deriv (complexSlope 3 t) v‖ := by
  have hb := derivative_affine_bound t x ht hx w hr hi hp hs v hv
  let A : ℂ := -(4 : ℂ)*Complex.I*(x : ℂ)
  have hA : ‖A‖ = 4*x := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (show 0 < x by linarith),mul_one]
  have hn := norm_sub_le (deriv (complexSlope 3 t) v) (deriv (complexSlope 3 t) v-A)
  rw [sub_sub_cancel,hA] at hn
  change ‖deriv (complexSlope 3 t) v-A‖ ≤ 2*x at hb
  linarith

theorem corrected_saddle_geometry (v : ℂ) (hv : v ∈ closedBall w (1/x)) :
    1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 := by
  have hx0 : 0 < x := by linarith
  have hpol := polynomial_bound t x ht w hp
  have hdist : ‖v-w‖ ≤ 1/x := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hd2 : ‖v-w‖ ≤ 2/x := hdist.trans ((div_le_div_iff_of_pos_right hx0).mpr (by norm_num))
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
    have he : (Complex.exp (4*v)).re = Real.exp (4*v.re)*Real.cos (4*v.im) := by
      simp [Complex.exp_re,Complex.mul_re,Complex.mul_im]
    have hh : 0 < (Complex.exp (4*v)).re := by linarith [hdom.2.1]
    rw [he] at hh
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hh
  have hlt : |4*v.im| < Real.pi/2 := by
    by_contra hn
    have hh := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt hn)
      (by rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 4)]; linarith [Real.pi_gt_three] :
        |4*v.im| ≤ Real.pi+Real.pi/2)
    rw [Real.cos_abs] at hh
    linarith
  refine ⟨by linarith [(abs_le.mp hre).1],?_,RiemannThetaComplexKernel.kernel_ne_zero v hdom.1 hdom.2.1⟩
  rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hlt
  linarith

theorem inverse_distance_bound (v q : ℂ) (hv : v ∈ closedBall w (1/x)) (hq : q ∈ closedBall w (1/x)) :
    2*x*‖v-q‖ ≤ ‖complexSlope 3 t v-complexSlope 3 t q‖ := by
  let A : ℂ := -(4 : ℂ)*Complex.I*(x : ℂ)
  have hA : ‖A‖ = 4*x := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (show 0 < x by linarith),mul_one]
  have ha := neighbor_slope_analytic t x ht (by linarith) w (by linarith) hi hs (polynomial_bound t x ht w hp)
  have hd : ∀ v ∈ closedBall w (1/x), DifferentiableAt ℂ (complexSlope 3 t) v := by
    intro v hv
    exact (ha v (closedBall_subset_closedBall ((div_le_div_iff_of_pos_right
      (show (0 : ℝ) < x by linarith)).mpr (by norm_num)) hv)).differentiableAt
  have hb : ∀ v ∈ closedBall w (1/x), ‖deriv (complexSlope 3 t) v-A‖ ≤ ‖A‖/2 := by
    intro v hv
    rw [hA]
    exact (derivative_affine_bound t x ht hx w hr hi hp hs v hv).trans_eq (by ring)
  have h := RiemannQuarticFrequencyBranch.scalar_ball_lower_bound (complexSlope 3 t) w A (1/x) hd hb v q hv hq
  rw [hA] at h
  nlinarith

def branch (z : ℂ) : ℂ :=
  if hz : ‖z-(x : ℂ)‖ ≤ 1 then
    Classical.choose (actual_far_frequency_disk t x ht hx w hr hi hp hs z hz).exists
  else w

theorem branch_spec (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    branch t x ht hx w hr hi hp hs z ∈ closedBall w (1/x) ∧
      complexSlope 3 t (branch t x ht hx w hr hi hp hs z) = -(Complex.I*z) := by
  simp only [branch,dite_eq_left hz]
  exact Classical.choose_spec (actual_far_frequency_disk t x ht hx w hr hi hp hs z hz).exists

theorem branch_distance (z y : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) (hy : ‖y-(x : ℂ)‖ ≤ 1) :
    ‖branch t x ht hx w hr hi hp hs z-branch t x ht hx w hr hi hp hs y‖ ≤ ‖z-y‖/(2*x) := by
  have hzs := branch_spec t x ht hx w hr hi hp hs z hz
  have hys := branch_spec t x ht hx w hr hi hp hs y hy
  have h := inverse_distance_bound t x ht hx w hr hi hp hs _ _ hzs.1 hys.1
  rw [hzs.2,hys.2,show -(Complex.I*z)-(-(Complex.I*y)) = -Complex.I*(z-y) by ring,
    norm_mul,norm_neg,Complex.norm_I,one_mul] at h
  exact (le_div_iff₀ (by linarith : 0 < 2*x)).mpr (by nlinarith)

theorem branch_lipschitz : LipschitzOnWith 1 (branch t x ht hx w hr hi hp hs) (closedBall (x : ℂ) 1) := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro z hz y hy
  have h := branch_distance t x ht hx w hr hi hp hs z y
    (by simpa only [mem_closedBall,dist_eq_norm] using hz)
    (by simpa only [mem_closedBall,dist_eq_norm] using hy)
  have hm := (le_div_iff₀ (by linarith : 0 < 2*x)).mp h
  norm_num only [NNReal.coe_one,one_mul]
  nlinarith [norm_nonneg (branch t x ht hx w hr hi hp hs z-branch t x ht hx w hr hi hp hs y)]

theorem branch_continuousAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    ContinuousAt (branch t x ht hx w hr hi hp hs) z := by
  have hz' : z ∈ ball (x : ℂ) 1 := by simpa only [mem_ball,dist_eq_norm] using hz
  have hn : closedBall (x : ℂ) 1 ∈ nhds z := mem_of_superset (isOpen_ball.mem_nhds hz') ball_subset_closedBall
  exact ((branch_lipschitz t x ht hx w hr hi hp hs).continuousOn z (ball_subset_closedBall hz')).continuousAt hn

theorem branch_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    AnalyticAt ℂ (branch t x ht hx w hr hi hp hs) z := by
  let v := branch t x ht hx w hr hi hp hs z
  have hspec := branch_spec t x ht hx w hr hi hp hs z hz.le
  have ha : AnalyticAt ℂ (complexSlope 3 t) v :=
    neighbor_slope_analytic t x ht (by linarith) w (by linarith) hi hs (polynomial_bound t x ht w hp) v
      (closedBall_subset_closedBall ((div_le_div_iff_of_pos_right
        (show (0 : ℝ) < x by linarith)).mpr (by norm_num)) hspec.1)
  have hn : deriv (complexSlope 3 t) v ≠ 0 := by
    have h := derivative_norm_lower t x ht hx w hr hi hp hs v hspec.1
    exact norm_pos_iff.mp (by linarith)
  let inv := ha.hasStrictDerivAt.localInverse (complexSlope 3 t) (deriv (complexSlope 3 t) v) v hn
  have hi' : AnalyticAt ℂ inv (-(Complex.I*z)) := by
    rw [← hspec.2]
    exact ha.analyticAt_localInverse hn
  have hc : AnalyticAt ℂ (fun y : ℂ => inv (-(Complex.I*y))) z :=
    AnalyticAt.comp (g := inv) (f := fun y : ℂ => -(Complex.I*y)) hi' (by fun_prop)
  have hleft : ∀ᶠ q in nhds v, inv (complexSlope 3 t q) = q := ha.hasStrictDerivAt.eventually_left_inverse hn
  have hleft' := (branch_continuousAt t x ht hx w hr hi hp hs z hz).tendsto.eventually hleft
  have hz' : z ∈ ball (x : ℂ) 1 := by simpa only [mem_ball,dist_eq_norm] using hz
  have he : branch t x ht hx w hr hi hp hs =ᶠ[nhds z] (fun y => inv (-(Complex.I*y))) := by
    filter_upwards [hleft',isOpen_ball.mem_nhds hz'] with y hy hys
    have hys' : ‖y-(x : ℂ)‖ ≤ 1 :=
      (show ‖y-(x : ℂ)‖ < 1 by simpa only [mem_ball,dist_eq_norm] using hys).le
    rw [(branch_spec t x ht hx w hr hi hp hs y hys').2] at hy
    exact hy.symm
  exact hc.congr he.symm

theorem branch_hasStrictDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    HasStrictDerivAt (branch t x ht hx w hr hi hp hs)
      (-Complex.I/deriv (complexSlope 3 t) (branch t x ht hx w hr hi hp hs z)) z := by
  have hb := branch_analyticAt t x ht hx w hr hi hp hs z hz
  have hspec := branch_spec t x ht hx w hr hi hp hs z hz.le
  have ha := neighbor_slope_analytic t x ht (by linarith) w (by linarith) hi hs
    (polynomial_bound t x ht w hp) _ (closedBall_subset_closedBall
      ((div_le_div_iff_of_pos_right (show (0 : ℝ) < x by linarith)).mpr (by norm_num)) hspec.1)
  have hn : deriv (complexSlope 3 t) (branch t x ht hx w hr hi hp hs z) ≠ 0 := by
    have h := derivative_norm_lower t x ht hx w hr hi hp hs _ hspec.1
    exact norm_pos_iff.mp (by linarith)
  have hd := ha.differentiableAt.hasDerivAt.comp z hb.differentiableAt.hasDerivAt
  have hz' : z ∈ ball (x : ℂ) 1 := by simpa only [mem_ball,dist_eq_norm] using hz
  have he : (fun y => complexSlope 3 t (branch t x ht hx w hr hi hp hs y)) =ᶠ[nhds z]
      (fun y : ℂ => -Complex.I*y) := by
    filter_upwards [isOpen_ball.mem_nhds hz'] with y hy
    have hy' : ‖y-(x : ℂ)‖ ≤ 1 :=
      (show ‖y-(x : ℂ)‖ < 1 by simpa only [mem_ball,dist_eq_norm] using hy).le
    simpa only [neg_mul] using (branch_spec t x ht hx w hr hi hp hs y hy').2
  have hde : deriv (complexSlope 3 t) (branch t x ht hx w hr hi hp hs z)*
      deriv (branch t x ht hx w hr hi hp hs) z = -Complex.I := by
    have hneg : HasDerivAt (fun y : ℂ => -Complex.I*y) (-Complex.I) z := by
      simpa using ((hasDerivAt_id z).const_mul (-Complex.I))
    exact (hd.congr_of_eventuallyEq he.symm).unique hneg
  have hderiv : deriv (branch t x ht hx w hr hi hp hs) z =
      -Complex.I/deriv (complexSlope 3 t) (branch t x ht hx w hr hi hp hs z) := by
    apply (eq_div_iff hn).mpr
    simpa only [mul_comm] using hde
  rw [← hderiv]
  exact hb.hasStrictDerivAt

theorem branch_deriv_norm_bound (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    ‖deriv (branch t x ht hx w hr hi hp hs) z‖ ≤ 1/(2*x) := by
  have hspec := branch_spec t x ht hx w hr hi hp hs z hz.le
  rw [(branch_hasStrictDerivAt t x ht hx w hr hi hp hs z hz).hasDerivAt.deriv,norm_div,norm_neg,Complex.norm_I]
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith : 0 < 2*x)
    (derivative_norm_lower t x ht hx w hr hi hp hs _ hspec.1)

theorem branch_domain (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    1 ≤ (branch t x ht hx w hr hi hp hs z).re ∧
      |(branch t x ht hx w hr hi hp hs z).im| < Real.pi/8 ∧
      kernelComplex (branch t x ht hx w hr hi hp hs z) ≠ 0 :=
  corrected_saddle_geometry t x ht hx w hr hi hp hs _ (branch_spec t x ht hx w hr hi hp hs z hz).1

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarAnalyticBranch
