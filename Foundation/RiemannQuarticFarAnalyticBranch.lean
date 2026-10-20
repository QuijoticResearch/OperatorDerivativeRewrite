import Foundation.RiemannQuarticFarPairing
/-! Coherent actual far-saddle selection on a unit complex frequency disk.
The actual weight phase is distinguished from the model-Gaussian amplitude phase. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarAnalyticBranch
open RiemannQuarticFarCorrection RiemannQuarticFrequencyBranch RiemannQuarticSaddleTheta
open RiemannQuarticSaddleBranch RiemannThetaComplexKernel

private theorem polynomial_bound (t x : ℝ) (ht : 1 ≤ t) (w : ℂ)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) : 4*t*‖w‖^3+9 ≤ x := by
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hm := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ t)
  nlinarith [pow_nonneg (norm_nonneg w) 3]

variable (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
  (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
  (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))

include ht hx hr hi hp hs

theorem derivative_affine_bound (v : ℂ) (hv : v ∈ closedBall w (1/x)) :
    ‖deriv (complexSlope t) v-(-(4 : ℂ)*Complex.I*(x : ℂ))‖ ≤ 2*x := by
  have hpol := polynomial_bound t x ht w hp
  have h1 := neighbor_error_deriv_bound t x ht (by linarith) w v (by linarith) hi hs hpol hv
  have h2 := model_deriv_near_far_saddle t x ht hx w v hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have h3 := norm_add_le (deriv (complexSlope t) v-deriv (modelDerivative t) v)
    (deriv (modelDerivative t) v-(-(4 : ℂ)*Complex.I*(x : ℂ)))
  rw [sub_add_sub_cancel] at h3
  have hm := mul_le_mul_of_nonneg_right (small_error_at_large_real_part w.re hr)
    (by linarith : 0 ≤ x)
  linarith

theorem inverse_distance_bound (v q : ℂ) (hv : v ∈ closedBall w (1/x))
    (hq : q ∈ closedBall w (1/x)) :
    2*x*‖v-q‖ ≤ ‖complexSlope t v-complexSlope t q‖ := by
  let A := -(4 : ℂ)*Complex.I*(x : ℂ)
  have hA : ‖A‖=4*x := by
    simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (by linarith : 0 < x),mul_one]
  have ha := neighbor_slope_analytic t x ht (by linarith) w (by linarith) hi hs
    (polynomial_bound t x ht w hp)
  have hd : ∀ v ∈ closedBall w (1/x), DifferentiableAt ℂ (complexSlope t) v := by
    intro v hv
    exact (ha v (closedBall_subset_closedBall ((div_le_div_iff_of_pos_right (show (0 : ℝ) < x by linarith)).mpr (by norm_num)) hv)).differentiableAt
  have hb : ∀ v ∈ closedBall w (1/x), ‖deriv (complexSlope t) v-A‖ ≤ ‖A‖/2 := by
    intro v hv
    rw [hA]
    exact (derivative_affine_bound t x ht hx w hr hi hp hs v hv).trans_eq (by ring)
  have h := scalar_ball_lower_bound (complexSlope t) w A (1/x) hd hb v q hv hq
  rw [hA] at h
  nlinarith

def branch (z : ℂ) : ℂ :=
  if hz : ‖z-(x : ℂ)‖ ≤ 1 then
    Classical.choose (actual_far_frequency_disk t x ht hx w hr hi hp hs z hz).exists
  else w

theorem branch_spec (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    branch t x ht hx w hr hi hp hs z ∈ closedBall w (1/x) ∧
      complexSlope t (branch t x ht hx w hr hi hp hs z)= -(Complex.I*z) := by
  simp only [branch,dite_eq_left hz]
  exact Classical.choose_spec (actual_far_frequency_disk t x ht hx w hr hi hp hs z hz).exists

theorem branch_distance (z y : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) (hy : ‖y-(x : ℂ)‖ ≤ 1) :
    ‖branch t x ht hx w hr hi hp hs z-branch t x ht hx w hr hi hp hs y‖ ≤ ‖z-y‖/(2*x) := by
  have hzs := branch_spec t x ht hx w hr hi hp hs z hz
  have hys := branch_spec t x ht hx w hr hi hp hs y hy
  have h := inverse_distance_bound t x ht hx w hr hi hp hs _ _ hzs.1 hys.1
  rw [hzs.2,hys.2,show -(Complex.I*z)-(-(Complex.I*y))= -Complex.I*(z-y) by ring,
    norm_mul,norm_neg,Complex.norm_I,one_mul] at h
  exact (le_div_iff₀ (by linarith : 0 < 2*x)).mpr (by nlinarith)

theorem branch_lipschitz : LipschitzOnWith 1 (branch t x ht hx w hr hi hp hs)
    (closedBall (x : ℂ) 1) := by
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
  have hn : closedBall (x : ℂ) 1 ∈ nhds z :=
    mem_of_superset (isOpen_ball.mem_nhds hz') ball_subset_closedBall
  exact ((branch_lipschitz t x ht hx w hr hi hp hs).continuousOn z (ball_subset_closedBall hz')).continuousAt hn

theorem branch_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    AnalyticAt ℂ (branch t x ht hx w hr hi hp hs) z := by
  let v := branch t x ht hx w hr hi hp hs z
  have hspec := branch_spec t x ht hx w hr hi hp hs z hz.le
  have ha : AnalyticAt ℂ (complexSlope t) v :=
    neighbor_slope_analytic t x ht (by linarith) w (by linarith) hi hs
      (polynomial_bound t x ht w hp) v
      (closedBall_subset_closedBall ((div_le_div_iff_of_pos_right (show (0 : ℝ) < x by linarith)).mpr (by norm_num)) hspec.1)
  have hn : deriv (complexSlope t) v ≠ 0 := by
    have h := actual_far_deriv_norm_lower t x ht hx w v hr hi hp hs hspec.1
    exact norm_pos_iff.mp (by linarith)
  let inv := ha.hasStrictDerivAt.localInverse (complexSlope t) (deriv (complexSlope t) v) v hn
  have hi' : AnalyticAt ℂ inv (-(Complex.I*z)) := by
    rw [← hspec.2]
    exact ha.analyticAt_localInverse hn
  have hc : AnalyticAt ℂ (fun y : ℂ => inv (-(Complex.I*y))) z := by
    exact AnalyticAt.comp (g := inv) (f := fun y : ℂ => -(Complex.I*y)) hi' (by fun_prop)
  have hleft : ∀ᶠ q in nhds v, inv (complexSlope t q)=q :=
    ha.hasStrictDerivAt.eventually_left_inverse hn
  have hleft' := (branch_continuousAt t x ht hx w hr hi hp hs z hz).tendsto.eventually hleft
  have hz' : z ∈ ball (x : ℂ) 1 := by simpa only [mem_ball,dist_eq_norm] using hz
  have he : branch t x ht hx w hr hi hp hs =ᶠ[nhds z] (fun y => inv (-(Complex.I*y))) := by
    filter_upwards [hleft',isOpen_ball.mem_nhds hz'] with y hy hys
    have hys' : ‖y-(x : ℂ)‖ ≤ 1 := by
      exact (show ‖y-(x : ℂ)‖ < 1 by simpa only [mem_ball,dist_eq_norm] using hys).le
    rw [(branch_spec t x ht hx w hr hi hp hs y hys').2] at hy
    exact hy.symm
  exact hc.congr he.symm

theorem branch_hasStrictDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    HasStrictDerivAt (branch t x ht hx w hr hi hp hs)
      (-Complex.I/deriv (complexSlope t) (branch t x ht hx w hr hi hp hs z)) z := by
  have hb := branch_analyticAt t x ht hx w hr hi hp hs z hz
  have hspec := branch_spec t x ht hx w hr hi hp hs z hz.le
  have ha := neighbor_slope_analytic t x ht (by linarith) w (by linarith) hi hs
    (polynomial_bound t x ht w hp) _
    (closedBall_subset_closedBall ((div_le_div_iff_of_pos_right (show (0 : ℝ) < x by linarith)).mpr (by norm_num)) hspec.1)
  have hn : deriv (complexSlope t) (branch t x ht hx w hr hi hp hs z) ≠ 0 := by
    have h := actual_far_deriv_norm_lower t x ht hx w _ hr hi hp hs hspec.1
    exact norm_pos_iff.mp (by linarith)
  have hd := ha.differentiableAt.hasDerivAt.comp z hb.differentiableAt.hasDerivAt
  have hz' : z ∈ ball (x : ℂ) 1 := by simpa only [mem_ball,dist_eq_norm] using hz
  have he : (fun y => complexSlope t (branch t x ht hx w hr hi hp hs y)) =ᶠ[nhds z]
      (fun y : ℂ => -Complex.I*y) := by
    filter_upwards [isOpen_ball.mem_nhds hz'] with y hy
    have hy' : ‖y-(x : ℂ)‖ ≤ 1 :=
      (show ‖y-(x : ℂ)‖ < 1 by simpa only [mem_ball,dist_eq_norm] using hy).le
    simpa only [neg_mul] using (branch_spec t x ht hx w hr hi hp hs y hy').2
  have hde : deriv (complexSlope t) (branch t x ht hx w hr hi hp hs z)*
      deriv (branch t x ht hx w hr hi hp hs) z = -Complex.I := by
    have hneg : HasDerivAt (fun y : ℂ => -Complex.I*y) (-Complex.I) z := by
      simpa using ((hasDerivAt_id z).const_mul (-Complex.I))
    exact (hd.congr_of_eventuallyEq he.symm).unique hneg
  have hderiv : deriv (branch t x ht hx w hr hi hp hs) z=
      -Complex.I/deriv (complexSlope t) (branch t x ht hx w hr hi hp hs z) := by
    apply (eq_div_iff hn).mpr
    simpa only [mul_comm] using hde
  rw [← hderiv]
  exact hb.hasStrictDerivAt

theorem branch_deriv_norm_bound (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    ‖deriv (branch t x ht hx w hr hi hp hs) z‖ ≤ 1/(2*x) := by
  have hspec := branch_spec t x ht hx w hr hi hp hs z hz.le
  rw [(branch_hasStrictDerivAt t x ht hx w hr hi hp hs z hz).hasDerivAt.deriv,
    norm_div,norm_neg,Complex.norm_I]
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith : 0 < 2*x)
    (actual_far_deriv_norm_lower t x ht hx w _ hr hi hp hs hspec.1)

theorem branch_domain (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    1 ≤ (branch t x ht hx w hr hi hp hs z).re ∧
    |(branch t x ht hx w hr hi hp hs z).im| < Real.pi/8 ∧
    kernelComplex (branch t x ht hx w hr hi hp hs z) ≠ 0 := by
  exact corrected_saddle_geometry t x ht hx w _ hr hi hp hs
    (branch_spec t x ht hx w hr hi hp hs z hz).1

theorem actual_weight_hasDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    HasDerivAt (fun y => saddleWeight t y (branch t x ht hx w hr hi hp hs y))
      (Complex.I*branch t x ht hx w hr hi hp hs z*
        saddleWeight t z (branch t x ht hx w hr hi hp hs z)) z := by
  let v := branch t x ht hx w hr hi hp hs z
  let d := -Complex.I/deriv (complexSlope t) v
  have hb : HasDerivAt (branch t x ht hx w hr hi hp hs) d z :=
    (branch_hasStrictDerivAt t x ht hx w hr hi hp hs z hz).hasDerivAt
  have hdom := branch_domain t x ht hx w hr hi hp hs z hz.le
  have hparam : 0 < (Complex.exp (4*v)).re :=
    RiemannQuarticKernelReflection.strip_domain v (by
      change -Real.pi/8 < v.im ∧ v.im < Real.pi/8
      simpa only [neg_div] using (abs_lt.mp hdom.2.1))
  have hk := kernelComplex_hasDerivAt v hparam
  have hslope := (branch_spec t x ht hx w hr hi hp hs z hz.le).2
  change 4*(t : ℂ)*v^3+deriv kernelComplex v/kernelComplex v= -(Complex.I*z) at hslope
  rw [hk.deriv] at hslope
  have hstation : 4*(t : ℂ)*v^3*kernelComplex v+kernelDerivative v=
      -(Complex.I*z)*kernelComplex v := by
    have hdiv : kernelDerivative v/kernelComplex v= -(Complex.I*z)-4*(t : ℂ)*v^3 := by
      linear_combination hslope
    have hm := (div_eq_iff hdom.2.2).mp hdiv
    linear_combination hm
  have he := ((hb.pow 4).const_mul (t : ℂ)).add
    ((((hasDerivAt_id z).const_mul Complex.I).mul hb))
  have hp' := he.cexp.mul (hk.comp z hb)
  convert hp' using 1
  · funext y
    rfl
  · change Complex.I*v*(Complex.exp ((t : ℂ)*v^4+Complex.I*z*v)*kernelComplex v)=
      Complex.exp ((t : ℂ)*v^4+Complex.I*z*v)*
        ((t : ℂ)*(4*v^3*d)+(Complex.I*1*v+Complex.I*z*d))*kernelComplex v+
      Complex.exp ((t : ℂ)*v^4+Complex.I*z*v)*(kernelDerivative v*d)
    linear_combination -Complex.exp ((t : ℂ)*v^4+Complex.I*z*v)*d*hstation

theorem actual_weight_ne_zero (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    saddleWeight t z (branch t x ht hx w hr hi hp hs z) ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (branch_domain t x ht hx w hr hi hp hs z hz).2.2

theorem actual_weight_logDerivative (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    deriv (fun y => saddleWeight t y (branch t x ht hx w hr hi hp hs y)) z/
      saddleWeight t z (branch t x ht hx w hr hi hp hs z)=
        Complex.I*branch t x ht hx w hr hi hp hs z := by
  rw [(actual_weight_hasDerivAt t x ht hx w hr hi hp hs z hz).deriv]
  exact mul_div_cancel_right₀ _ (actual_weight_ne_zero t x ht hx w hr hi hp hs z hz.le)

theorem exists_normalized_weight_phase : ∃ P : ℂ → ℂ, P (x : ℂ)=0 ∧
    ∀ z ∈ ball (x : ℂ) 1, HasDerivAt P (Complex.I*branch t x ht hx w hr hi hp hs z) z := by
  have hd : DifferentiableOn ℂ (fun z => Complex.I*branch t x ht hx w hr hi hp hs z)
      (ball (x : ℂ) 1) := by
    intro z hz
    have hz' : ‖z-(x : ℂ)‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hz
    exact ((branch_analyticAt t x ht hx w hr hi hp hs z hz').differentiableAt.const_mul Complex.I).differentiableWithinAt
  exact hd.isExactOn_ball.with_val_at (x : ℂ) 0

theorem actual_weight_eq_exp_phase (P : ℂ → ℂ) (hP0 : P (x : ℂ)=0)
    (hP : ∀ z ∈ ball (x : ℂ) 1, HasDerivAt P (Complex.I*branch t x ht hx w hr hi hp hs z) z)
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    saddleWeight t z (branch t x ht hx w hr hi hp hs z)=
      saddleWeight t (x : ℂ) (branch t x ht hx w hr hi hp hs (x : ℂ))*Complex.exp (P z) := by
  let F := fun y => saddleWeight t y (branch t x ht hx w hr hi hp hs y)*Complex.exp (-P y)
  have hd : ∀ y ∈ ball (x : ℂ) 1, HasDerivAt F 0 y := by
    intro y hy
    have hy' : ‖y-(x : ℂ)‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hy
    have h := (actual_weight_hasDerivAt t x ht hx w hr hi hp hs y hy').mul (hP y hy).neg.cexp
    convert h using 1 <;> ring
  have hz' : z ∈ ball (x : ℂ) 1 := by simpa only [mem_ball,dist_eq_norm] using hz
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (x : ℂ) 1).isPreconnected
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv) hz' (mem_ball_self (by norm_num : (0 : ℝ)<1))
  change saddleWeight t z (branch t x ht hx w hr hi hp hs z)*Complex.exp (-P z)=
    saddleWeight t (x : ℂ) (branch t x ht hx w hr hi hp hs (x : ℂ))*Complex.exp (-P (x : ℂ)) at he
  rw [hP0,neg_zero,Complex.exp_zero,mul_one] at he
  have hm := congrArg (fun c => c*Complex.exp (P z)) he
  rw [mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,mul_one] at hm
  exact hm

theorem weight_phase_real_derivative (P : ℂ → ℂ)
    (hP : ∀ z ∈ ball (x : ℂ) 1, HasDerivAt P (Complex.I*branch t x ht hx w hr hi hp hs z) z)
    (y : ℝ) (hy : |y-x| < 1) :
    HasDerivAt (fun a : ℝ => (P (a : ℂ)).im) (branch t x ht hx w hr hi hp hs (y : ℂ)).re y ∧
      120019 ≤ (branch t x ht hx w hr hi hp hs (y : ℂ)).re := by
  have hy' : ‖(y : ℂ)-(x : ℂ)‖ < 1 := by
    simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hy
  have hyball : (y : ℂ) ∈ ball (x : ℂ) 1 := by simpa only [mem_ball,dist_eq_norm] using hy'
  have hd := ((hP (y : ℂ) hyball).const_mul (-Complex.I)).real_of_complex
  have hder : HasDerivAt (fun a : ℝ => (P (a : ℂ)).im)
      (branch t x ht hx w hr hi hp hs (y : ℂ)).re y := by
    simpa only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
      neg_zero,zero_mul,neg_neg,one_mul,Complex.mul_im,mul_one,mul_zero,sub_zero,zero_add,
      neg_one_mul,sub_neg_eq_add] using hd
  refine ⟨hder,?_⟩
  have hv := (branch_spec t x ht hx w hr hi hp hs (y : ℂ) hy'.le).1
  have hn : ‖branch t x ht hx w hr hi hp hs (y : ℂ)-w‖ ≤ 1 := by
    have h := (show ‖branch t x ht hx w hr hi hp hs (y : ℂ)-w‖ ≤ 1/x by
      simpa only [mem_closedBall,dist_eq_norm] using hv)
    exact h.trans ((div_le_iff₀ (by linarith : 0 < x)).mpr (by linarith))
  have hre := (Complex.abs_re_le_norm (branch t x ht hx w hr hi hp hs (y : ℂ)-w)).trans hn
  simp only [Complex.sub_re] at hre
  linarith [(abs_le.mp hre).1]

theorem weight_phase_real_growth (P : ℂ → ℂ)
    (hP : ∀ z ∈ ball (x : ℂ) 1, HasDerivAt P (Complex.I*branch t x ht hx w hr hi hp hs z) z)
    (a b : ℝ) (ha : a ∈ Ioo (x-1) (x+1)) (hb : b ∈ Ioo (x-1) (x+1)) (hab : a ≤ b) :
    120019*(b-a) ≤ (P (b : ℂ)).im-(P (a : ℂ)).im := by
  have hd (y : ℝ) (hy : y ∈ Ioo (x-1) (x+1)) :=
    weight_phase_real_derivative t x ht hx w hr hi hp hs P hP y (by
      rw [abs_lt]
      constructor <;> linarith [hy.1,hy.2])
  exact (convex_Ioo (x-1) (x+1)).mul_sub_le_image_sub_of_le_deriv
    (fun y hy => (hd y hy).1.continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).1.differentiableAt.differentiableWithinAt)
    (fun y hy => by rw [(hd y (interior_subset hy)).1.deriv]; exact (hd y (interior_subset hy)).2)
    a ha b hb hab

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarAnalyticBranch
