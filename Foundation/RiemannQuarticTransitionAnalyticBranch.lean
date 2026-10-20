import Foundation.RiemannQuarticTransitionReflection
import Foundation.RiemannQuarticFarAnalyticBranch
/-! Coherent actual saddle selection on transition frequency disks.
The phase below belongs to the actual arithmetic weight, not yet the
Gaussian amplitude or the paired cosine approximation. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionAnalyticBranch
open RiemannQuarticTransitionCorrection RiemannQuarticTransitionCompact
open RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch RiemannQuarticFrequencyBranch
open RiemannThetaComplexKernel RiemannQuarticFarModelSaddle

section Scaled
variable (t K x r : ℝ) (w : ℂ)
  (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hnorm : ‖w‖ ≤ 2*w.re) (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
  (hE : ‖Complex.exp (4*w)‖ ≤ K)
  (hsmall : (30005*Real.exp (-w.re))*K ≤ t*w.re^3/4)
  (hrpos : 0 < r) (hradius : r ≤ t*w.re^3/K)
include ht hK hr hi hnorm hs hE hsmall hrpos hradius

theorem inverse_distance_bound (v q : ℂ) (hv : v ∈ closedBall w (1/K))
    (hq : q ∈ closedBall w (1/K)) :
    2*(t*w.re^3)*‖v-q‖ ≤ ‖complexSlope t v-complexSlope t q‖ := by
  let A : ℂ := -(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)
  have hA := scaled_curvature_lower t (x : ℂ) w ht (by linarith) hi (by simp) hs
  have ha := scaled_neighbor_analytic t K (x : ℂ) w ht hK (by linarith) hi (by simp) hs hE
  have hsub : closedBall w (1/K) ⊆ closedBall w (2/K) :=
    closedBall_subset_closedBall (by apply (div_le_div_iff_of_pos_right (show 0 < K by linarith)).mpr; norm_num)
  have hd : ∀ v ∈ closedBall w (1/K), DifferentiableAt ℂ (complexSlope t) v :=
    fun v hv => (ha v (hsub hv)).differentiableAt
  have hb : ∀ v ∈ closedBall w (1/K), ‖deriv (complexSlope t) v-A‖ ≤ ‖A‖/2 := by
    intro v hv
    exact scaled_actual_deriv_bound t K (x : ℂ) w v ht hK (by linarith) hi hnorm (by simp) hs hE hsmall hv
  have h := scalar_ball_lower_bound (complexSlope t) w A (1/K) hd hb v q hv hq
  have hm := mul_le_mul_of_nonneg_right hA (norm_nonneg (v-q))
  nlinarith

def branch (z : ℂ) : ℂ :=
  if hz : ‖z-(x : ℂ)‖ ≤ r then
    Classical.choose (actual_scaled_frequency_disk t K (x : ℂ) w z ht hK (by linarith)
      hi hnorm (by simp) hs hE hsmall (hz.trans hradius)).exists
  else w

theorem branch_spec (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z ∈ closedBall w (1/K) ∧
      complexSlope t (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z)= -(Complex.I*z) := by
  simp only [branch,dite_eq_left hz]
  exact Classical.choose_spec (actual_scaled_frequency_disk t K (x : ℂ) w z ht hK
    (by linarith) hi hnorm (by simp) hs hE hsmall (hz.trans hradius)).exists

theorem branch_distance (z y : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) (hy : ‖y-(x : ℂ)‖ ≤ r) :
    ‖branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z-branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius y‖ ≤ ‖z-y‖/(2*(t*w.re^3)) := by
  have hzs := branch_spec t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz
  have hys := branch_spec t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius y hy
  have h := inverse_distance_bound t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius _ _ hzs.1 hys.1
  rw [hzs.2,hys.2,show -(Complex.I*z)-(-(Complex.I*y))= -Complex.I*(z-y) by ring,
    norm_mul,norm_neg,Complex.norm_I,one_mul] at h
  exact (le_div_iff₀ (by positivity : 0 < 2*(t*w.re^3))).mpr (by nlinarith)

theorem branch_lipschitz : LipschitzOnWith 1 (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius) (closedBall (x : ℂ) r) := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro z hz y hy
  have h := branch_distance t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z y
    (by simpa only [mem_closedBall,dist_eq_norm] using hz)
    (by simpa only [mem_closedBall,dist_eq_norm] using hy)
  have hm := (le_div_iff₀ (by positivity : 0 < 2*(t*w.re^3))).mp h
  have hQ : 1 ≤ t*w.re^3 := by
    have hp : 1 ≤ w.re^3 := one_le_pow₀ (by linarith : 1 ≤ w.re)
    nlinarith
  norm_num only [NNReal.coe_one,one_mul]
  nlinarith [norm_nonneg (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z-branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius y)]

theorem branch_continuousAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    ContinuousAt (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius) z := by
  have hz' : z ∈ ball (x : ℂ) r := by simpa only [mem_ball,dist_eq_norm] using hz
  have hn : closedBall (x : ℂ) r ∈ nhds z :=
    mem_of_superset (isOpen_ball.mem_nhds hz') ball_subset_closedBall
  exact ((branch_lipschitz t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius).continuousOn z (ball_subset_closedBall hz')).continuousAt hn

theorem branch_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    AnalyticAt ℂ (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius) z := by
  let v := branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z
  have hspec := branch_spec t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz.le
  have ha : AnalyticAt ℂ (complexSlope t) v :=
    scaled_neighbor_analytic t K (x : ℂ) w ht hK (by linarith) hi (by simp) hs hE v
      (closedBall_subset_closedBall (by apply (div_le_div_iff_of_pos_right (show 0 < K by linarith)).mpr; norm_num) hspec.1)
  have hn : deriv (complexSlope t) v ≠ 0 := by
    have h := scaled_actual_deriv_lower t K (x : ℂ) w v ht hK (by linarith) hi hnorm (by simp) hs hE hsmall hspec.1
    exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < 2*t*w.re^3) h)
  let inv := ha.hasStrictDerivAt.localInverse (complexSlope t) (deriv (complexSlope t) v) v hn
  have hi' : AnalyticAt ℂ inv (-(Complex.I*z)) := by
    rw [← hspec.2]
    exact ha.analyticAt_localInverse hn
  have hc : AnalyticAt ℂ (fun y : ℂ => inv (-(Complex.I*y))) z := by
    exact AnalyticAt.comp (g := inv) (f := fun y : ℂ => -(Complex.I*y)) hi' (by fun_prop)
  have hleft : ∀ᶠ q in nhds v, inv (complexSlope t q)=q :=
    ha.hasStrictDerivAt.eventually_left_inverse hn
  have hleft' := (branch_continuousAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz).tendsto.eventually hleft
  have hz' : z ∈ ball (x : ℂ) r := by simpa only [mem_ball,dist_eq_norm] using hz
  have he : branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius =ᶠ[nhds z] (fun y => inv (-(Complex.I*y))) := by
    filter_upwards [hleft',isOpen_ball.mem_nhds hz'] with y hy hys
    have hys' : ‖y-(x : ℂ)‖ ≤ r := by
      exact (show ‖y-(x : ℂ)‖ < r by simpa only [mem_ball,dist_eq_norm] using hys).le
    rw [(branch_spec t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius y hys').2] at hy
    exact hy.symm
  exact hc.congr he.symm

theorem branch_hasStrictDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    HasStrictDerivAt (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius)
      (-Complex.I/deriv (complexSlope t) (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z)) z := by
  have hb := branch_analyticAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz
  have hspec := branch_spec t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz.le
  have ha := scaled_neighbor_analytic t K (x : ℂ) w ht hK (by linarith) hi (by simp) hs hE _
    (closedBall_subset_closedBall (by apply (div_le_div_iff_of_pos_right (show 0 < K by linarith)).mpr; norm_num) hspec.1)
  have hn : deriv (complexSlope t) (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z) ≠ 0 := by
    have h := scaled_actual_deriv_lower t K (x : ℂ) w _ ht hK (by linarith) hi hnorm (by simp) hs hE hsmall hspec.1
    exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < 2*t*w.re^3) h)
  have hd := ha.differentiableAt.hasDerivAt.comp z hb.differentiableAt.hasDerivAt
  have hz' : z ∈ ball (x : ℂ) r := by simpa only [mem_ball,dist_eq_norm] using hz
  have he : (fun y => complexSlope t (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius y)) =ᶠ[nhds z]
      (fun y : ℂ => -Complex.I*y) := by
    filter_upwards [isOpen_ball.mem_nhds hz'] with y hy
    have hy' : ‖y-(x : ℂ)‖ ≤ r :=
      (show ‖y-(x : ℂ)‖ < r by simpa only [mem_ball,dist_eq_norm] using hy).le
    simpa only [neg_mul] using (branch_spec t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius y hy').2
  have hde : deriv (complexSlope t) (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z)*
      deriv (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius) z = -Complex.I := by
    have hneg : HasDerivAt (fun y : ℂ => -Complex.I*y) (-Complex.I) z := by
      simpa using ((hasDerivAt_id z).const_mul (-Complex.I))
    exact (hd.congr_of_eventuallyEq he.symm).unique hneg
  have hderiv : deriv (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius) z=
      -Complex.I/deriv (complexSlope t) (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z) := by
    apply (eq_div_iff hn).mpr
    simpa only [mul_comm] using hde
  rw [← hderiv]
  exact hb.hasStrictDerivAt

theorem branch_deriv_norm_bound (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    ‖deriv (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius) z‖ ≤ 1/(2*(t*w.re^3)) := by
  have hspec := branch_spec t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz.le
  rw [(branch_hasStrictDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz).hasDerivAt.deriv,
    norm_div,norm_neg,Complex.norm_I]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity : 0 < 2*(t*w.re^3))
    (by simpa only [mul_assoc] using
      (scaled_actual_deriv_lower t K (x : ℂ) w _ ht hK (by linarith) hi hnorm (by simp) hs hE hsmall hspec.1))

theorem branch_domain (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    1 ≤ (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z).re ∧
    |(branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z).im| < Real.pi/8 ∧
    kernelComplex (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z) ≠ 0 := by
  have hg := corrected_geometry t K (x : ℂ) w (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z) ht hK hr hi hnorm
    (by simp) hs hE (by simpa only [mem_closedBall,dist_eq_norm] using
      (branch_spec t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz).1)
  exact ⟨by linarith [hg.1], hg.2⟩

theorem actual_weight_hasDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    HasDerivAt (fun y => saddleWeight t y (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius y))
      (Complex.I*branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z*
        saddleWeight t z (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z)) z := by
  let v := branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z
  let d := -Complex.I/deriv (complexSlope t) v
  have hb : HasDerivAt (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius) d z :=
    (branch_hasStrictDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz).hasDerivAt
  have hdom := branch_domain t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz.le
  have hparam : 0 < (Complex.exp (4*v)).re :=
    RiemannQuarticKernelReflection.strip_domain v (by
      change -Real.pi/8 < v.im ∧ v.im < Real.pi/8
      simpa only [neg_div] using (abs_lt.mp hdom.2.1))
  have hk := kernelComplex_hasDerivAt v hparam
  have hslope := (branch_spec t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz.le).2
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

theorem actual_weight_ne_zero (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    saddleWeight t z (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z) ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (branch_domain t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz).2.2

theorem actual_weight_logDerivative (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    deriv (fun y => saddleWeight t y (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius y)) z/
      saddleWeight t z (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z)=
        Complex.I*branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z := by
  rw [(actual_weight_hasDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz).deriv]
  exact mul_div_cancel_right₀ _ (actual_weight_ne_zero t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz.le)

theorem exists_normalized_weight_phase : ∃ P : ℂ → ℂ, P (x : ℂ)=0 ∧
    ∀ z ∈ ball (x : ℂ) r, HasDerivAt P (Complex.I*branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z) z := by
  have hd : DifferentiableOn ℂ (fun z => Complex.I*branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z)
      (ball (x : ℂ) r) := by
    intro z hz
    have hz' : ‖z-(x : ℂ)‖ < r := by simpa only [mem_ball,dist_eq_norm] using hz
    exact ((branch_analyticAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz').differentiableAt.const_mul Complex.I).differentiableWithinAt
  exact hd.isExactOn_ball.with_val_at (x : ℂ) 0

theorem actual_weight_eq_exp_phase (P : ℂ → ℂ) (hP0 : P (x : ℂ)=0)
    (hP : ∀ z ∈ ball (x : ℂ) r, HasDerivAt P (Complex.I*branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z) z)
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    saddleWeight t z (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z)=
      saddleWeight t (x : ℂ) (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius (x : ℂ))*Complex.exp (P z) := by
  let F := fun y => saddleWeight t y (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius y)*Complex.exp (-P y)
  have hd : ∀ y ∈ ball (x : ℂ) r, HasDerivAt F 0 y := by
    intro y hy
    have hy' : ‖y-(x : ℂ)‖ < r := by simpa only [mem_ball,dist_eq_norm] using hy
    have h := (actual_weight_hasDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius y hy').mul (hP y hy).neg.cexp
    convert h using 1 <;> ring
  have hz' : z ∈ ball (x : ℂ) r := by simpa only [mem_ball,dist_eq_norm] using hz
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (x : ℂ) r).isPreconnected
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv) hz' (mem_ball_self hrpos)
  change saddleWeight t z (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius z)*Complex.exp (-P z)=
    saddleWeight t (x : ℂ) (branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius (x : ℂ))*Complex.exp (-P (x : ℂ)) at he
  rw [hP0,neg_zero,Complex.exp_zero,mul_one] at he
  have hm := congrArg (fun c => c*Complex.exp (P z)) he
  rw [mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,mul_one] at hm
  exact hm


end Scaled

theorem exists_actual_transition_phase (t u M x : ℝ)
    (ht : 1 ≤ t) (hM : 0 ≤ M) (hu : 65536*(M+7) ≤ u)
    (hstationary : RiemannQuarticSaddleTimes.phaseSlope t u=0)
    (hx : |x| ≤ M*RiemannQuarticTransitionSaddle.realScale u) :
    ∃ (w : ℂ) (b P : ℂ → ℂ),
      ‖w-(u : ℂ)‖ ≤ M+7 ∧ P (x : ℂ)=0 ∧
      (∀ z : ℂ, ‖z-(x : ℂ)‖ ≤ 1/(128*(M+8)) →
        ‖b z-w‖ ≤ 1/((M+8)*RiemannQuarticTransitionSaddle.realScale u) ∧
        complexSlope t (b z)= -(Complex.I*z) ∧
        |(b z).im| < Real.pi/8 ∧ kernelComplex (b z) ≠ 0) ∧
      (∀ z : ℂ, ‖z-(x : ℂ)‖ < 1/(128*(M+8)) →
        AnalyticAt ℂ b z ∧
        HasStrictDerivAt b (-Complex.I/deriv (complexSlope t) (b z)) z ∧
        HasDerivAt P (Complex.I*b z) z ∧
        ‖deriv b z‖ ≤ 1/(2*(t*w.re^3)) ∧
        ‖deriv P z-Complex.I*w‖ ≤ 1/((M+8)*RiemannQuarticTransitionSaddle.realScale u) ∧
        saddleWeight t z (b z)=saddleWeight t (x : ℂ) (b (x : ℂ))*Complex.exp (P z)) := by
  let K := (M+8)*RiemannQuarticTransitionSaddle.realScale u
  let C := 128*(M+8)
  let r := 1/C
  have hC : 0 < C := by dsimp [C]; positivity
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hxnorm : ‖(x : ℂ)‖ ≤ M*RiemannQuarticTransitionSaddle.realScale u := by simpa using hx
  obtain ⟨w,hw,_⟩ := RiemannQuarticTransitionSaddle.existsUnique_transition_model_saddle
    t u M (x : ℂ) ht hM hu hstationary (by simp) hxnorm
  have hg := RiemannQuarticTransitionSaddle.transition_model_geometry t u M (x : ℂ) w
    ht hM hu hstationary (by simp) hxnorm hw.1 hw.2
  have hd := transition_scale_data t u M (x : ℂ) w ht hM hu hstationary (by simp) hxnorm hw.1 hw.2
  have hK : 8 ≤ K := hd.1
  have hnorm := hd.2.2.2.1
  have hE := hd.2.2.2.2.1
  have hsmall := hd.2.2.2.2.2
  have hcoord := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hg.1
  simp only [Complex.sub_re,Complex.ofReal_re] at hcoord
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hcoord).1]
  have hscale : K ≤ C*(t*w.re^3) :=
    RiemannQuarticTransitionGaussian.moving_scale_ratio_bound t u M w ht hM hu hstationary hg.1
  have hradius : r ≤ t*w.re^3/K := by
    apply (le_div_iff₀ (by linarith : 0 < K)).mpr
    dsimp [r]
    have hh : K/C ≤ t*w.re^3 := (div_le_iff₀ hC).mpr (by nlinarith)
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
  let b := branch t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hradius
  obtain ⟨P,hP0,hP⟩ := exists_normalized_weight_phase t K x r w ht hK hr hd.2.2.1
    hnorm hw.2 hE hsmall hrpos hradius
  refine ⟨w,b,P,hg.1,hP0,?_,?_⟩
  · intro z hz
    have hspec := branch_spec t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hz
    have hdom := branch_domain t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hz
    exact ⟨by simpa only [mem_closedBall,dist_eq_norm] using hspec.1,hspec.2,hdom.2⟩
  · intro z hz
    have hzball : z ∈ ball (x : ℂ) r := by simpa only [mem_ball,dist_eq_norm] using hz
    have hphase := hP z hzball
    have hdist := (branch_spec t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hz.le).1
    have hpbound : ‖deriv P z-Complex.I*w‖ ≤ 1/K := by
      rw [hphase.deriv, ← mul_sub, norm_mul, Complex.norm_I, one_mul]
      simpa only [mem_closedBall,dist_eq_norm] using hdist
    exact ⟨branch_analyticAt t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hz,
      branch_hasStrictDerivAt t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hz,
      hphase, branch_deriv_norm_bound t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hz,
      hpbound, actual_weight_eq_exp_phase t K x r w ht hK hr hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius P hP0 hP z hz⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionAnalyticBranch
