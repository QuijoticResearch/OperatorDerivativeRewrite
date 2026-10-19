import Foundation.RiemannQuarticQuantitativeSaddle
import Mathlib.Analysis.Complex.HasPrimitives
/-! Coherent analytic saddle branch and actual exponential saddle phase.
The branch exists uniquely on the closed frequency disk, is analytic on its
interior, and has the exact inverse derivative and quantitative displacement.
The actual saddle weight exp(t*w^4+i*z*w)*Phi(w) is nonzero, has logarithmic
derivative i*w, and equals its zero-frequency value times exp(P) for a
normalized primitive P. Its third derivative satisfies 25600/(t*u^3+1)^2.
No Gaussian prefactor, contour deformation or integrated remainder is proved. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFrequencyBranch
open RiemannQuarticQuantitativeSaddle RiemannQuarticSaddleBranch RiemannQuarticSaddleTimes
open RiemannQuarticSaddleNeighborhood

theorem scalar_ball_lower_bound (f : ℂ → ℂ) (b a : ℂ) (r : ℝ)
    (hd : ∀ w ∈ closedBall b r, DifferentiableAt ℂ f w)
    (hb : ∀ w ∈ closedBall b r, ‖deriv f w-a‖ ≤ ‖a‖/2)
    (x y : ℂ) (hx : x ∈ closedBall b r) (hy : y ∈ closedBall b r) :
    (‖a‖/2)*‖x-y‖ ≤ ‖f x-f y‖ := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hd w hw).sub ((hasDerivAt_id w).const_mul a).differentiableAt)
    (fun w hw => by
      rw [deriv_sub (hd w hw) ((hasDerivAt_id w).const_mul a).differentiableAt,
        ((hasDerivAt_id w).const_mul a).deriv]
      simpa using hb w hw)
    (convex_closedBall b r) hy hx
  simp only [Pi.sub_apply,id_eq] at h
  have he : f x-a*x-(f y-a*y)=f x-f y-a*(x-y) := by ring
  rw [he] at h
  have hn := norm_sub_le (f x-f y) (f x-f y-a*(x-y))
  rw [show f x-f y-(f x-f y-a*(x-y))=a*(x-y) by ring,norm_mul] at hn
  linarith

def branch (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0) (z : ℂ) : ℂ :=
  if hz : ‖z‖ ≤ (t*u^3+1)/51200 then
    Classical.choose (existsUnique_frequency_saddle t u ht hu hs z hz).exists
  else (u : ℂ)

theorem branch_spec (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ ≤ (t*u^3+1)/51200) :
    branch t u ht hu hs z ∈ closedBall (u : ℂ) (1/102400) ∧
      complexSlope t (branch t u ht hu hs z)= -(Complex.I*z) := by
  simp only [branch,dite_eq_left hz]
  exact Classical.choose_spec (existsUnique_frequency_saddle t u ht hu hs z hz).exists

theorem branch_zero (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0) :
    branch t u ht hu hs 0=(u : ℂ) := by
  have hz : ‖(0 : ℂ)‖ ≤ (t*u^3+1)/51200 := by simp only [norm_zero]; positivity
  apply (existsUnique_frequency_saddle t u ht hu hs 0 hz).unique
    (branch_spec t u ht hu hs 0 hz)
  constructor
  · simp
  · rw [complexSlope_real,hs]; simp

theorem branch_lipschitz (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0) :
    LipschitzOnWith 1 (branch t u ht hu hs) (closedBall (0 : ℂ) ((t*u^3+1)/51200)) := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro z hz y hy
  have hz' : ‖z‖ ≤ (t*u^3+1)/51200 := by simpa using hz
  have hy' : ‖y‖ ≤ (t*u^3+1)/51200 := by simpa using hy
  have hzspec := branch_spec t u ht hu hs z hz'
  have hyspec := branch_spec t u ht hu hs y hy'
  have hd : ∀ w ∈ closedBall (u : ℂ) (1/102400), DifferentiableAt ℂ (complexSlope t) w := by
    intro w hw
    exact (slope_analytic_on_neighborhood t u hu w
      (closedBall_subset_closedBall (by norm_num) hw)).differentiableAt
  have h := scalar_ball_lower_bound (complexSlope t) (u : ℂ)
    (deriv (complexSlope t) (u : ℂ)) (1/102400) hd
    (stationary_slope_deriv_near_center t u ht hu hs) _ _ hzspec.1 hyspec.1
  rw [hzspec.2,hyspec.2] at h
  have he : -(Complex.I*z)-(-(Complex.I*y))= -Complex.I*(z-y) := by ring
  rw [he,norm_mul,norm_neg,Complex.norm_I,one_mul] at h
  have hl := stationary_slope_deriv_norm_lower t u ht hu hs
  have hq : 0 ≤ t*u^3 := by positivity
  have hp := mul_le_mul_of_nonneg_right hl (norm_nonneg (branch t u ht hu hs z-branch t u ht hu hs y))
  have hqq := mul_nonneg hq (norm_nonneg (branch t u ht hu hs z-branch t u ht hu hs y))
  norm_num only [NNReal.coe_one,one_mul]
  nlinarith [norm_nonneg (branch t u ht hu hs z-branch t u ht hu hs y)]

theorem branch_continuousAt (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) : ContinuousAt (branch t u ht hu hs) z := by
  have hz' : z ∈ ball (0 : ℂ) ((t*u^3+1)/51200) := by simpa using hz
  have hn : closedBall (0 : ℂ) ((t*u^3+1)/51200) ∈ nhds z :=
    mem_of_superset (isOpen_ball.mem_nhds hz') ball_subset_closedBall
  exact ((branch_lipschitz t u ht hu hs).continuousOn z (ball_subset_closedBall hz')).continuousAt hn

theorem branch_analyticAt (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) : AnalyticAt ℂ (branch t u ht hu hs) z := by
  let w := branch t u ht hu hs z
  have hspec := branch_spec t u ht hu hs z hz.le
  have ha : AnalyticAt ℂ (complexSlope t) w :=
    slope_analytic_on_neighborhood t u hu w (closedBall_subset_closedBall (by norm_num) hspec.1)
  have hn : deriv (complexSlope t) w ≠ 0 := frequency_saddle_deriv_ne_zero t u ht hu hs w hspec.1
  let inv := ha.hasStrictDerivAt.localInverse (complexSlope t) (deriv (complexSlope t) w) w hn
  have hi : AnalyticAt ℂ inv (-(Complex.I*z)) := by
    rw [← hspec.2]
    exact ha.analyticAt_localInverse hn
  have hc : AnalyticAt ℂ (fun y : ℂ => inv (-(Complex.I*y))) z := by
    have hneg : AnalyticAt ℂ (fun y : ℂ => -(Complex.I*y)) z := by fun_prop
    exact AnalyticAt.comp (g := inv) (f := fun y : ℂ => -(Complex.I*y)) hi hneg
  have hleft : ∀ᶠ v in nhds w, inv (complexSlope t v)=v :=
    ha.hasStrictDerivAt.eventually_left_inverse hn
  have hcont := branch_continuousAt t u ht hu hs z hz
  have hleft' := hcont.tendsto.eventually hleft
  have hz' : z ∈ ball (0 : ℂ) ((t*u^3+1)/51200) := by simpa using hz
  have hnear : ∀ᶠ y in nhds z, ‖y‖ ≤ (t*u^3+1)/51200 := by
    filter_upwards [isOpen_ball.mem_nhds hz'] with y hy
    have hy' : ‖y‖ < (t*u^3+1)/51200 := by simpa using hy
    exact hy'.le
  have he : branch t u ht hu hs =ᶠ[nhds z] (fun y => inv (-(Complex.I*y))) := by
    filter_upwards [hleft',hnear] with y hy hys
    rw [(branch_spec t u ht hu hs y hys).2] at hy
    exact hy.symm
  exact hc.congr he.symm


theorem branch_hasStrictDerivAt (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) :
    HasStrictDerivAt (branch t u ht hu hs)
      (-Complex.I/deriv (complexSlope t) (branch t u ht hu hs z)) z := by
  have hb := branch_analyticAt t u ht hu hs z hz
  have hspec := branch_spec t u ht hu hs z hz.le
  have ha := slope_analytic_on_neighborhood t u hu _
    (closedBall_subset_closedBall (by norm_num) hspec.1)
  have hn := frequency_saddle_deriv_ne_zero t u ht hu hs _ hspec.1
  have hd := ha.differentiableAt.hasDerivAt.comp z hb.differentiableAt.hasDerivAt
  have he : (fun y => complexSlope t (branch t u ht hu hs y)) =ᶠ[nhds z]
      (fun y : ℂ => -Complex.I*y) := by
    have hz' : z ∈ ball (0 : ℂ) ((t*u^3+1)/51200) := by simpa using hz
    filter_upwards [isOpen_ball.mem_nhds hz'] with y hy
    have hy' : ‖y‖ < (t*u^3+1)/51200 := by simpa using hy
    simpa only [neg_mul] using (branch_spec t u ht hu hs y hy'.le).2
  have hde : deriv (complexSlope t) (branch t u ht hu hs z)*
      deriv (branch t u ht hu hs) z = -Complex.I := by
    have hneg : HasDerivAt (fun y : ℂ => -Complex.I*y) (-Complex.I) z := by
      simpa using ((hasDerivAt_id z).const_mul (-Complex.I))
    exact (hd.congr_of_eventuallyEq he.symm).unique hneg
  have hederiv : deriv (branch t u ht hu hs) z =
      -Complex.I/deriv (complexSlope t) (branch t u ht hu hs z) := by
    apply (eq_div_iff hn).mpr
    simpa only [mul_comm] using hde
  rw [← hederiv]
  exact hb.hasStrictDerivAt

theorem branch_domain (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ ≤ (t*u^3+1)/51200) :
    0 < (Complex.exp (4*branch t u ht hu hs z)).re ∧
      RiemannThetaComplexKernel.kernelComplex (branch t u ht hu hs z) ≠ 0 :=
  frequency_saddle_domain t u hu _ (branch_spec t u ht hu hs z hz).1

theorem branch_analyticOnNhd (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0) :
    AnalyticOnNhd ℂ (branch t u ht hu hs) (ball (0 : ℂ) ((t*u^3+1)/51200)) := by
  intro z hz
  apply branch_analyticAt t u ht hu hs z
  simpa using hz


open RiemannThetaComplexKernel

def saddleWeight (t : ℝ) (z w : ℂ) : ℂ :=
  Complex.exp ((t : ℂ)*w^4+Complex.I*z*w)*kernelComplex w

theorem saddleWeight_ne_zero (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ ≤ (t*u^3+1)/51200) :
    saddleWeight t z (branch t u ht hu hs z) ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (branch_domain t u ht hu hs z hz).2

theorem saddleWeight_hasDerivAt (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) :
    HasDerivAt (fun y => saddleWeight t y (branch t u ht hu hs y))
      (Complex.I*branch t u ht hu hs z*saddleWeight t z (branch t u ht hu hs z)) z := by
  let w := branch t u ht hu hs z
  let d := -Complex.I/deriv (complexSlope t) w
  have hb : HasDerivAt (branch t u ht hu hs) d z :=
    (branch_hasStrictDerivAt t u ht hu hs z hz).hasDerivAt
  have hdom := branch_domain t u ht hu hs z hz.le
  have hk := kernelComplex_hasDerivAt w hdom.1
  have hslope := (branch_spec t u ht hu hs z hz.le).2
  change 4*(t : ℂ)*w^3+deriv kernelComplex w/kernelComplex w= -(Complex.I*z) at hslope
  rw [hk.deriv] at hslope
  have hstation : 4*(t : ℂ)*w^3*kernelComplex w+kernelDerivative w=
      -(Complex.I*z)*kernelComplex w := by
    have hdiv : kernelDerivative w/kernelComplex w= -(Complex.I*z)-4*(t : ℂ)*w^3 := by
      linear_combination hslope
    have hm := (div_eq_iff hdom.2).mp hdiv
    linear_combination hm
  have he := ((hb.pow 4).const_mul (t : ℂ)).add
    ((((hasDerivAt_id z).const_mul Complex.I).mul hb))
  have hp := he.cexp.mul (hk.comp z hb)
  convert hp using 1
  · funext y
    rfl
  · change Complex.I*w*(Complex.exp ((t : ℂ)*w^4+Complex.I*z*w)*kernelComplex w)=
      Complex.exp ((t : ℂ)*w^4+Complex.I*z*w)*
        ((t : ℂ)*(4*w^3*d)+(Complex.I*1*w+Complex.I*z*d))*kernelComplex w+
      Complex.exp ((t : ℂ)*w^4+Complex.I*z*w)*(kernelDerivative w*d)
    linear_combination -Complex.exp ((t : ℂ)*w^4+Complex.I*z*w)*d*hstation

theorem saddleWeight_logDerivative (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) :
    deriv (fun y => saddleWeight t y (branch t u ht hu hs y)) z/
      saddleWeight t z (branch t u ht hu hs z)=Complex.I*branch t u ht hu hs z := by
  rw [(saddleWeight_hasDerivAt t u ht hu hs z hz).deriv]
  exact mul_div_cancel_right₀ _ (saddleWeight_ne_zero t u ht hu hs z hz.le)


theorem saddleWeight_logDerivative_hasDerivAt (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) :
    HasDerivAt (fun y => deriv (fun v => saddleWeight t v (branch t u ht hu hs v)) y/
      saddleWeight t y (branch t u ht hu hs y))
      (deriv (complexSlope t) (branch t u ht hu hs z))⁻¹ z := by
  have hb := (branch_hasStrictDerivAt t u ht hu hs z hz).hasDerivAt.const_mul Complex.I
  have hn := frequency_saddle_deriv_ne_zero t u ht hu hs _ (branch_spec t u ht hu hs z hz.le).1
  have he : Complex.I*(-Complex.I/deriv (complexSlope t) (branch t u ht hu hs z))=
      (deriv (complexSlope t) (branch t u ht hu hs z))⁻¹ := by
    field_simp
    simp [Complex.I_sq]
  rw [he] at hb
  apply hb.congr_of_eventuallyEq
  have hz' : z ∈ ball (0 : ℂ) ((t*u^3+1)/51200) := by simpa using hz
  filter_upwards [isOpen_ball.mem_nhds hz'] with y hy
  have hy' : ‖y‖ < (t*u^3+1)/51200 := by simpa using hy
  exact saddleWeight_logDerivative t u ht hu hs y hy'


theorem branch_scaled_distance (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z y : ℂ) (hz : ‖z‖ ≤ (t*u^3+1)/51200) (hy : ‖y‖ ≤ (t*u^3+1)/51200) :
    (2*(t*u^3+1))*‖branch t u ht hu hs z-branch t u ht hu hs y‖ ≤ ‖z-y‖ := by
  have hzspec := branch_spec t u ht hu hs z hz
  have hyspec := branch_spec t u ht hu hs y hy
  have hd : ∀ w ∈ closedBall (u : ℂ) (1/102400), DifferentiableAt ℂ (complexSlope t) w := by
    intro w hw
    exact (slope_analytic_on_neighborhood t u hu w
      (closedBall_subset_closedBall (by norm_num) hw)).differentiableAt
  have h := scalar_ball_lower_bound (complexSlope t) (u : ℂ)
    (deriv (complexSlope t) (u : ℂ)) (1/102400) hd
    (stationary_slope_deriv_near_center t u ht hu hs) _ _ hzspec.1 hyspec.1
  rw [hzspec.2,hyspec.2] at h
  have he : -(Complex.I*z)-(-(Complex.I*y))= -Complex.I*(z-y) := by ring
  rw [he,norm_mul,norm_neg,Complex.norm_I,one_mul] at h
  have hp := mul_le_mul_of_nonneg_right (stationary_slope_deriv_norm_lower t u ht hu hs)
    (norm_nonneg (branch t u ht hu hs z-branch t u ht hu hs y))
  nlinarith

theorem branch_displacement_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ ≤ (t*u^3+1)/51200) :
    ‖branch t u ht hu hs z-(u : ℂ)‖ ≤ ‖z‖/(2*(t*u^3+1)) := by
  have hq : 0 < 2*(t*u^3+1) := by positivity
  apply (le_div_iff₀ hq).mpr
  have hz0 : ‖(0 : ℂ)‖ ≤ (t*u^3+1)/51200 := by simp only [norm_zero]; positivity
  have h := branch_scaled_distance t u ht hu hs z 0 hz hz0
  rw [branch_zero,sub_zero] at h
  simpa only [mul_comm] using h

theorem slope_deriv_norm_lower_on_ball (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    2*(t*u^3+1) ≤ ‖deriv (complexSlope t) w‖ := by
  have hv := stationary_slope_deriv_near_center t u ht hu hs w hw
  have hl := stationary_slope_deriv_norm_lower t u ht hu hs
  have hn := norm_sub_le (deriv (complexSlope t) w)
    (deriv (complexSlope t) w-deriv (complexSlope t) (u : ℂ))
  rw [show deriv (complexSlope t) w-(deriv (complexSlope t) w-
    deriv (complexSlope t) (u : ℂ))=deriv (complexSlope t) (u : ℂ) by ring] at hn
  linarith

theorem branch_deriv_norm_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) :
    ‖deriv (branch t u ht hu hs) z‖ ≤ 1/(2*(t*u^3+1)) := by
  rw [(branch_hasStrictDerivAt t u ht hu hs z hz).hasDerivAt.deriv]
  rw [norm_div,norm_neg,Complex.norm_I]
  apply one_div_le_one_div_of_le (by positivity)
  exact slope_deriv_norm_lower_on_ball t u ht hu hs _ (branch_spec t u ht hu hs z hz.le).1


theorem inverseCurvature_hasDerivAt (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) :
    HasDerivAt (fun y => (deriv (complexSlope t) (branch t u ht hu hs y))⁻¹)
      (Complex.I*iteratedDeriv 2 (complexSlope t) (branch t u ht hu hs z)/
        (deriv (complexSlope t) (branch t u ht hu hs z))^3) z := by
  have hspec := branch_spec t u ht hu hs z hz.le
  have ha := slope_analytic_on_neighborhood t u hu _
    (closedBall_subset_closedBall (by norm_num) hspec.1)
  have hn := frequency_saddle_deriv_ne_zero t u ht hu hs _ hspec.1
  have hd := ha.deriv.differentiableAt.hasDerivAt.comp z
    (branch_hasStrictDerivAt t u ht hu hs z hz).hasDerivAt
  have hi := hd.inv hn
  convert hi using 1
  · rfl
  · simp only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero,Function.comp_apply]
    field_simp

theorem inverseCurvature_deriv_norm_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) :
    ‖deriv (fun y => (deriv (complexSlope t) (branch t u ht hu hs y))⁻¹) z‖ ≤
      25600/(t*u^3+1)^2 := by
  let Q := t*u^3+1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let w := branch t u ht hu hs z
  have hw := (branch_spec t u ht hu hs z hz.le).1
  have hl := slope_deriv_norm_lower_on_ball t u ht hu hs w hw
  have h2 := stationary_slope_inner_cauchy_bound t u ht hu hs w
    (closedBall_subset_closedBall (by norm_num) hw) 2
  norm_num only [Nat.factorial, Nat.cast_ofNat, pow_succ, pow_zero, mul_one] at h2
  have hsecond : ‖iteratedDeriv 2 (complexSlope t) w‖ ≤ 204800*Q := by
    convert h2 using 1 <;> dsimp [Q] <;> ring
  have hl' : 2*Q ≤ ‖deriv (complexSlope t) w‖ := hl
  have hden : 0 < ‖deriv (complexSlope t) w‖ := by linarith
  rw [(inverseCurvature_hasDerivAt t u ht hu hs z hz).deriv,
    norm_div,norm_mul,Complex.norm_I,one_mul,norm_pow]
  change ‖iteratedDeriv 2 (complexSlope t) w‖/‖deriv (complexSlope t) w‖^3 ≤ 25600/Q^2
  apply (div_le_iff₀ (pow_pos hden 3)).mpr
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 2*Q) hl' 3
  have hp := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 25600/Q^2)
  have he : (25600/Q^2)*(2*Q)^3=204800*Q := by
    field_simp
    ring
  rw [he] at hp
  exact hsecond.trans hp


theorem exists_normalized_phase (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0) :
    ∃ P : ℂ → ℂ, P 0=0 ∧ ∀ z ∈ ball (0 : ℂ) ((t*u^3+1)/51200),
      HasDerivAt P (Complex.I*branch t u ht hu hs z) z := by
  have hd : DifferentiableOn ℂ (fun z => Complex.I*branch t u ht hu hs z)
      (ball (0 : ℂ) ((t*u^3+1)/51200)) := by
    intro z hz
    have hz' : ‖z‖ < (t*u^3+1)/51200 := by simpa using hz
    exact ((branch_analyticAt t u ht hu hs z hz').differentiableAt.const_mul Complex.I).differentiableWithinAt
  exact hd.isExactOn_ball.with_val_at 0 0

theorem saddleWeight_eq_exp_phase (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (P : ℂ → ℂ) (hP0 : P 0=0)
    (hP : ∀ z ∈ ball (0 : ℂ) ((t*u^3+1)/51200), HasDerivAt P (Complex.I*branch t u ht hu hs z) z)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) :
    saddleWeight t z (branch t u ht hu hs z)=saddleWeight t 0 (u : ℂ)*Complex.exp (P z) := by
  let F := fun y => saddleWeight t y (branch t u ht hu hs y)*Complex.exp (-P y)
  have hd : ∀ y ∈ ball (0 : ℂ) ((t*u^3+1)/51200), HasDerivAt F 0 y := by
    intro y hy
    have hy' : ‖y‖ < (t*u^3+1)/51200 := by simpa using hy
    have h := (saddleWeight_hasDerivAt t u ht hu hs y hy').mul (hP y hy).neg.cexp
    convert h using 1 <;> ring
  have hr : 0 < (t*u^3+1)/51200 := by positivity
  have hz' : z ∈ ball (0 : ℂ) ((t*u^3+1)/51200) := by simpa using hz
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) _).isPreconnected
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv) hz' (mem_ball_self hr)
  change saddleWeight t z (branch t u ht hu hs z)*Complex.exp (-P z)=
    saddleWeight t 0 (branch t u ht hu hs 0)*Complex.exp (-P 0) at he
  rw [hP0,neg_zero,Complex.exp_zero,mul_one,branch_zero] at he
  have hm := congrArg (fun c => c*Complex.exp (P z)) he
  rw [mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,mul_one] at hm
  exact hm


theorem phase_hasSecondDerivAt (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (P : ℂ → ℂ)
    (hP : ∀ z ∈ ball (0 : ℂ) ((t*u^3+1)/51200), HasDerivAt P (Complex.I*branch t u ht hu hs z) z)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) :
    HasDerivAt (deriv P) (deriv (complexSlope t) (branch t u ht hu hs z))⁻¹ z := by
  apply (saddleWeight_logDerivative_hasDerivAt t u ht hu hs z hz).congr_of_eventuallyEq
  have hz' : z ∈ ball (0 : ℂ) ((t*u^3+1)/51200) := by simpa using hz
  filter_upwards [isOpen_ball.mem_nhds hz'] with y hy
  have hy' : ‖y‖ < (t*u^3+1)/51200 := by simpa using hy
  rw [(hP y hy).deriv,saddleWeight_logDerivative t u ht hu hs y hy']

theorem phase_third_deriv_norm_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (P : ℂ → ℂ)
    (hP : ∀ z ∈ ball (0 : ℂ) ((t*u^3+1)/51200), HasDerivAt P (Complex.I*branch t u ht hu hs z) z)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) :
    ‖iteratedDeriv 3 P z‖ ≤ 25600/(t*u^3+1)^2 := by
  have hz' : z ∈ ball (0 : ℂ) ((t*u^3+1)/51200) := by simpa using hz
  have he : deriv (deriv P) =ᶠ[nhds z]
      (fun y => (deriv (complexSlope t) (branch t u ht hu hs y))⁻¹) := by
    filter_upwards [isOpen_ball.mem_nhds hz'] with y hy
    have hy' : ‖y‖ < (t*u^3+1)/51200 := by simpa using hy
    exact (phase_hasSecondDerivAt t u ht hu hs P hP y hy').deriv
  have h := inverseCurvature_deriv_norm_bound t u ht hu hs z hz
  rw [← he.deriv_eq] at h
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using h

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFrequencyBranch
