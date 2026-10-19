import Foundation.RiemannQuarticSaddleGeometry
import Foundation.RiemannQuarticPhaseRemainder
/-! Actual local spatial phase and signed Gaussian-model integral error.
A normalized primitive of G_t(w+v)+i*z represents the actual kernel weight.
At an actual saddle its quadratic phase error is <=204800*Q*norm(v)^3,
Q=t*u^3+1. Under the stated small-error radius condition, the SIGNED local
integral differs from the truncated quadratic Gaussian model by at most
819200*Q*r^4*norm(W_t(z,w)). Complementary horizontal tails and comparison
to the full Gaussian-normalized Fourier contribution remain separate. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticSpatialPhase
open RiemannQuarticSaddleBranch RiemannQuarticSaddleTimes RiemannQuarticSaddleNeighborhood
open RiemannQuarticQuantitativeSaddle RiemannQuarticFrequencyBranch RiemannQuarticPhaseRemainder
open RiemannThetaComplexKernel

theorem shifted_point_mem (u : ℝ) (w v : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/102400)) (hv : ‖v‖ ≤ 1/102400) :
    w+v ∈ closedBall (u : ℂ) (1/32) := by
  have hd : ‖w-(u : ℂ)‖ ≤ (1/102400 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have h := norm_add_le (w-(u : ℂ)) v
  rw [show w-(u : ℂ)+v=w+v-(u : ℂ) by ring] at h
  rw [mem_closedBall,dist_eq_norm]
  linarith

theorem spatial_weight_hasDerivAt (t : ℝ) (z v : ℂ)
    (hv : 0 < (Complex.exp (4*v)).re) (hk : kernelComplex v ≠ 0) :
    HasDerivAt (saddleWeight t z) ((complexSlope t v+Complex.I*z)*saddleWeight t z v) v := by
  have hd := kernelComplex_hasDerivAt v hv
  have hp := (((hasDerivAt_id v).pow 4).const_mul (t : ℂ)).add
    ((hasDerivAt_id v).const_mul (Complex.I*z))
  have h := hp.cexp.mul hd
  convert h using 1
  · funext y
    rfl
  · unfold complexSlope saddleWeight
    rw [hd.deriv]
    simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply,id_eq]
    field_simp [hk]
    ring

theorem local_slope_analyticAt (t u : ℝ) (hu : 1 ≤ u) (z w v : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/102400)) (hv : ‖v‖ < 1/102400) :
    AnalyticAt ℂ (fun y => complexSlope t (w+y)+Complex.I*z) v := by
  have hp := shifted_point_mem u w v hw hv.le
  have ha := slope_analytic_on_neighborhood t u hu (w+v)
    (closedBall_subset_closedBall (by norm_num) hp)
  have hadd : AnalyticAt ℂ (fun y : ℂ => w+y) v := by fun_prop
  exact (AnalyticAt.comp (g := complexSlope t) (f := fun y : ℂ => w+y) ha hadd).add analyticAt_const

theorem exists_local_phase (t u : ℝ) (hu : 1 ≤ u) (z w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    ∃ P : ℂ → ℂ, P 0=0 ∧ ∀ v ∈ ball (0 : ℂ) (1/102400),
      HasDerivAt P (complexSlope t (w+v)+Complex.I*z) v := by
  have hd : DifferentiableOn ℂ (fun v => complexSlope t (w+v)+Complex.I*z)
      (ball (0 : ℂ) (1/102400)) := by
    intro v hv
    exact (local_slope_analyticAt t u hu z w v hw (by simpa using hv)).differentiableAt.differentiableWithinAt
  exact hd.isExactOn_ball.with_val_at 0 0

theorem local_weight_eq_exp_phase (t u : ℝ) (hu : 1 ≤ u) (z w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/102400)) (P : ℂ → ℂ) (hP0 : P 0=0)
    (hP : ∀ v ∈ ball (0 : ℂ) (1/102400), HasDerivAt P (complexSlope t (w+v)+Complex.I*z) v)
    (v : ℂ) (hv : ‖v‖ < 1/102400) :
    saddleWeight t z (w+v)=saddleWeight t z w*Complex.exp (P v) := by
  let F := fun y => saddleWeight t z (w+y)*Complex.exp (-P y)
  have hd : ∀ y ∈ ball (0 : ℂ) (1/102400), HasDerivAt F 0 y := by
    intro y hy
    have hp := shifted_point_mem u w y hw (by simpa using (mem_ball.mp hy).le)
    have hdom := neighborhood_domain u hu (w+y) (closedBall_subset_closedBall (by norm_num) hp)
    have hn := kernel_nonzero_on_neighborhood u hu (w+y) (closedBall_subset_closedBall (by norm_num) hp)
    have hweight := (spatial_weight_hasDerivAt t z (w+y) (by linarith [hdom.2]) hn).comp y
      ((hasDerivAt_id y).const_add w)
    have h := hweight.mul (hP y hy).neg.cexp
    convert h using 1
    · funext a
      rfl
    · simp only [mul_one,Function.comp_apply,Pi.neg_apply]
      ring
  have hz0 : (0 : ℂ) ∈ ball (0 : ℂ) (1/102400) := mem_ball_self (by norm_num)
  have hv' : v ∈ ball (0 : ℂ) (1/102400) := by simpa using hv
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) _).isPreconnected
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv) hv' hz0
  change saddleWeight t z (w+v)*Complex.exp (-P v)=saddleWeight t z (w+0)*Complex.exp (-P 0) at he
  rw [hP0,add_zero,neg_zero,Complex.exp_zero,mul_one] at he
  have hm := congrArg (fun c => c*Complex.exp (P v)) he
  rw [mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,mul_one] at hm
  exact hm

theorem local_phase_second (t u : ℝ) (hu : 1 ≤ u) (z w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/102400)) (P : ℂ → ℂ)
    (hP : ∀ v ∈ ball (0 : ℂ) (1/102400), HasDerivAt P (complexSlope t (w+v)+Complex.I*z) v)
    (v : ℂ) (hv : ‖v‖ < 1/102400) :
    HasDerivAt (deriv P) (deriv (complexSlope t) (w+v)) v := by
  have hp := shifted_point_mem u w v hw hv.le
  have ha := slope_analytic_on_neighborhood t u hu (w+v)
    (closedBall_subset_closedBall (by norm_num) hp)
  have hd := (ha.differentiableAt.hasDerivAt.comp v ((hasDerivAt_id v).const_add w)).add_const (Complex.I*z)
  have hd' : HasDerivAt (fun y => complexSlope t (w+y)+Complex.I*z) (deriv (complexSlope t) (w+v)) v := by
    convert hd using 1 <;> first | rfl | simp only [mul_one,Function.comp_apply]
  apply hd'.congr_of_eventuallyEq
  have hv' : v ∈ ball (0 : ℂ) (1/102400) := by simpa using hv
  filter_upwards [isOpen_ball.mem_nhds hv'] with y hy
  exact (hP y hy).deriv

theorem local_phase_third_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) (P : ℂ → ℂ)
    (hP : ∀ v ∈ ball (0 : ℂ) (1/102400), HasDerivAt P (complexSlope t (w+v)+Complex.I*z) v)
    (v : ℂ) (hv : ‖v‖ < 1/102400) :
    ‖iteratedDeriv 3 P v‖ ≤ 204800*(t*u^3+1) := by
  have hp := shifted_point_mem u w v hw hv.le
  have ha := slope_analytic_on_neighborhood t u hu (w+v)
    (closedBall_subset_closedBall (by norm_num) hp)
  have hd := ha.deriv.differentiableAt.hasDerivAt.comp v ((hasDerivAt_id v).const_add w)
  have hd' : HasDerivAt (fun y => deriv (complexSlope t) (w+y))
      (deriv (deriv (complexSlope t)) (w+v)) v := by
    convert hd using 1 <;> first | rfl | simp only [mul_one,Function.comp_apply]
  have he : deriv (deriv P) =ᶠ[nhds v] (fun y => deriv (complexSlope t) (w+y)) := by
    have hv' : v ∈ ball (0 : ℂ) (1/102400) := by simpa using hv
    filter_upwards [isOpen_ball.mem_nhds hv'] with y hy
    exact (local_phase_second t u hu z w hw P hP y (by simpa using hy)).deriv
  have heq := he.deriv_eq
  rw [hd'.deriv] at heq
  have hb := stationary_slope_inner_cauchy_bound t u ht hu hs (w+v) hp 2
  norm_num only [Nat.factorial,Nat.cast_ofNat,pow_succ,pow_zero,mul_one] at hb
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hb ⊢
  rw [heq]
  convert hb using 1 <;> ring

theorem local_phase_quadratic_remainder (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) (hstat : complexSlope t w= -(Complex.I*z))
    (P : ℂ → ℂ) (hP0 : P 0=0)
    (hP : ∀ v ∈ ball (0 : ℂ) (1/102400), HasDerivAt P (complexSlope t (w+v)+Complex.I*z) v)
    (v : ℂ) (hv : ‖v‖ < 1/102400) :
    ‖P v-deriv (complexSlope t) w*v^2/2‖ ≤ (204800*(t*u^3+1))*‖v‖^3 := by
  have ha : AnalyticOnNhd ℂ P (ball (0 : ℂ) (1/102400)) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    intro y hy
    exact (hP y hy).differentiableAt.differentiableWithinAt
  have h := cubic_remainder_bound P (1/102400) (204800*(t*u^3+1)) (by positivity) ha
    (fun y hy => local_phase_third_bound t u ht hu hs z w hw P hP y (by simpa using hy)) v hv
  have h0 : deriv P 0=0 := by rw [(hP 0 (mem_ball_self (by norm_num))).deriv,add_zero,hstat]; ring
  have h00 : deriv (deriv P) 0=deriv (complexSlope t) w := by
    simpa using (local_phase_second t u hu z w hw P hP 0 (by norm_num)).deriv
  simpa only [hP0,h0,h00,sub_zero,zero_mul] using h


theorem local_weight_relative_error (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) (hstat : complexSlope t w= -(Complex.I*z))
    (v : ℂ) (hv : ‖v‖ < 1/102400) (hsmall : (204800*(t*u^3+1))*‖v‖^3 ≤ 1) :
    ‖saddleWeight t z (w+v)/(saddleWeight t z w*Complex.exp (deriv (complexSlope t) w*v^2/2))-1‖ ≤
      (409600*(t*u^3+1))*‖v‖^3 := by
  obtain ⟨P,hP0,hP⟩ := exists_local_phase t u hu z w hw
  have hrem := local_phase_quadratic_remainder t u ht hu hs z w hw hstat P hP0 hP v hv
  have hn : saddleWeight t z w ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _)
    (kernel_nonzero_on_neighborhood u hu w (closedBall_subset_closedBall (by norm_num) hw))
  have heq : saddleWeight t z (w+v)/(saddleWeight t z w*Complex.exp (deriv (complexSlope t) w*v^2/2))=
      Complex.exp (P v-deriv (complexSlope t) w*v^2/2) := by
    rw [local_weight_eq_exp_phase t u hu z w hw P hP0 hP v hv]
    rw [mul_div_mul_left _ _ hn,Complex.exp_sub]
  rw [heq]
  have he := Complex.norm_exp_sub_one_le (hrem.trans hsmall)
  calc
    _ ≤ 2*‖P v-deriv (complexSlope t) w*v^2/2‖ := he
    _ ≤ 2*((204800*(t*u^3+1))*‖v‖^3) := mul_le_mul_of_nonneg_left hrem (by norm_num)
    _ = _ := by ring


theorem local_weight_absolute_error (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) (hstat : complexSlope t w= -(Complex.I*z))
    (s : ℝ) (hv : |s| < 1/102400) (hsmall : (204800*(t*u^3+1))*|s|^3 ≤ 1) :
    ‖saddleWeight t z (w+(s : ℂ))-saddleWeight t z w*Complex.exp (deriv (complexSlope t) w*(s : ℂ)^2/2)‖ ≤
      (409600*(t*u^3+1))*|s|^3*‖saddleWeight t z w‖ := by
  have hrel := local_weight_relative_error t u ht hu hs z w hw hstat (s : ℂ)
    (by simpa using hv) (by simpa using hsmall)
  simp only [Complex.norm_real,Real.norm_eq_abs] at hrel
  let B := saddleWeight t z w*Complex.exp (deriv (complexSlope t) w*(s : ℂ)^2/2)
  have hn : saddleWeight t z w ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _)
    (kernel_nonzero_on_neighborhood u hu w (closedBall_subset_closedBall (by norm_num) hw))
  have hB : B ≠ 0 := mul_ne_zero hn (Complex.exp_ne_zero _)
  have hd := RiemannQuarticSaddleGeometry.slope_deriv_re_half_bound t u ht hu hs w hw
  have hdn := RiemannQuarticCurvature.stationary_phaseSlope_deriv_neg t u ht hu hs
  have hre : (deriv (complexSlope t) w*(s : ℂ)^2/2).re ≤ 0 := by
    simp only [Complex.div_ofNat_re,Complex.mul_re,← Complex.ofReal_pow,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]
    have hm := mul_nonpos_of_nonpos_of_nonneg (by linarith : (deriv (complexSlope t) w).re ≤ 0) (sq_nonneg s)
    linarith
  have hBn : ‖B‖ ≤ ‖saddleWeight t z w‖ := by
    dsimp [B]
    rw [norm_mul,Complex.norm_exp]
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hre) (norm_nonneg _)).trans_eq (mul_one _)
  have he : saddleWeight t z (w+(s : ℂ))-B=(saddleWeight t z (w+(s : ℂ))/B-1)*B := by
    field_simp
  change ‖saddleWeight t z (w+(s : ℂ))-B‖ ≤ _
  rw [he,norm_mul]
  exact mul_le_mul hrel hBn (norm_nonneg _) (by positivity)

theorem horizontal_weight_continuous (t u : ℝ) (z w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    Continuous (fun s : ℝ => saddleWeight t z (w+(s : ℂ))) := by
  have hd : ‖w-(u : ℂ)‖ ≤ (1/102400 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hi := (Complex.abs_im_le_norm (w-(u : ℂ))).trans hd
  have him : |w.im| ≤ 1/16 := by simpa using hi.trans (by norm_num : (1/102400 : ℝ) ≤ 1/16)
  apply continuous_iff_continuousAt.mpr
  intro s
  have ha := RiemannQuarticContour.weight_analyticAt t z (w+(s : ℂ)) (by simpa using him)
  have hc : ContinuousAt (fun a : ℝ => w+(a : ℂ)) s := by fun_prop
  exact ContinuousAt.comp (g := saddleWeight t z) (f := fun a : ℝ => w+(a : ℂ)) ha.continuousAt hc

theorem local_signed_integral_error (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) (hstat : complexSlope t w= -(Complex.I*z))
    (r : ℝ) (hr : 0 ≤ r) (hrr : r < 1/102400) (hsmall : (204800*(t*u^3+1))*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, saddleWeight t z (w+(s : ℂ)))-
      saddleWeight t z w*(∫ s : ℝ in -r..r, Complex.exp (deriv (complexSlope t) w*(s : ℂ)^2/2))‖ ≤
      (819200*(t*u^3+1))*r^4*‖saddleWeight t z w‖ := by
  have hf : IntervalIntegrable (fun s : ℝ => saddleWeight t z (w+(s : ℂ))) volume (-r) r :=
    (horizontal_weight_continuous t u z w hw).intervalIntegrable (-r) r
  have hg : IntervalIntegrable (fun s : ℝ => saddleWeight t z w*
      Complex.exp (deriv (complexSlope t) w*(s : ℂ)^2/2)) volume (-r) r :=
    (by fun_prop : Continuous (fun s : ℝ => saddleWeight t z w*
      Complex.exp (deriv (complexSlope t) w*(s : ℂ)^2/2))).intervalIntegrable (-r) r
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub hf hg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -r) (b := r) (C := (409600*(t*u^3+1))*r^3*‖saddleWeight t z w‖)
    (fun s hsi => by
      rw [uIoc_of_le (by linarith : -r ≤ r)] at hsi
      have habs : |s| ≤ r := abs_le.mpr ⟨hsi.1.le,hsi.2⟩
      have hp := pow_le_pow_left₀ (abs_nonneg s) habs 3
      have hss : (204800*(t*u^3+1))*|s|^3 ≤ 1 :=
        (mul_le_mul_of_nonneg_left hp (by positivity)).trans hsmall
      calc
        _ ≤ (409600*(t*u^3+1))*|s|^3*‖saddleWeight t z w‖ :=
          local_weight_absolute_error t u ht hu hs z w hw hstat s (habs.trans_lt hrr) hss
        _ ≤ _ := by gcongr)
  rw [show r-(-r)=2*r by ring,abs_of_nonneg (by positivity : 0 ≤ 2*r)] at hb
  convert hb using 1 <;> ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticSpatialPhase
