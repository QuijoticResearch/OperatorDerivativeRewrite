import Foundation.RiemannQuarticSaddleNeighborhood
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
/-! Quantitative complex saddles for the actual quartic Xi kernel.
At any real stationary point t>=0,u>=1, every complex frequency of norm
at most (t*u^3+1)/51200 has exactly one saddle within radius1/102400.
The kernel and slope derivative are nonzero there. For all sufficiently
large times this applies to every global positive-half-line amplitude maximum,
with frequency radius at least (t+1)/51200. These are pointwise inverse
existence/uniqueness results, not yet an analytic branch on the entire disk,
a contour deformation, Gaussian approximation or integrated remainder bound. -/
noncomputable section
open Set Metric
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticQuantitativeSaddle
open RiemannQuarticSaddleNeighborhood
open RiemannQuarticSaddleBranch

theorem inner_neighborhood_subset (u : ℝ) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/32)) :
    closedBall w (1/32) ⊆ closedBall (u : ℂ) (1/16) := by
  intro z hz
  have h := dist_triangle z w (u : ℂ)
  have hw' := mem_closedBall.mp hw
  have hz' := mem_closedBall.mp hz
  apply mem_closedBall.mpr
  linarith

theorem slope_error_inner_cauchy_bound (t u : ℝ) (hu : 1 ≤ u) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/32)) (n : ℕ) :
    ‖iteratedDeriv n (fun z => complexSlope t z-
        RiemannQuarticSaddleTheta.modelDerivative t z) w‖ ≤
      (n.factorial : ℝ)*(32 : ℝ)^n := by
  have hsub := inner_neighborhood_subset u w hw
  have ha := (slope_error_analytic_on_neighborhood t u hu).mono hsub
  have hd := ha.differentiableOn.diffContOnCl_ball (Set.Subset.refl _)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1/32) hd
    (fun z hz => slope_model_error_on_neighborhood t u hu z
      (hsub (sphere_subset_closedBall hz)))
  calc
    _ ≤ (n.factorial : ℝ)*1/((1/32 : ℝ)^n) := h
    _ = _ := by simp only [one_div,inv_pow,mul_one,div_inv_eq_mul]


theorem slope_error_inner_lipschitz (t u : ℝ) (hu : 1 ≤ u) (w z : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/32))
    (hz : z ∈ closedBall (u : ℂ) (1/32)) :
    ‖(complexSlope t z-RiemannQuarticSaddleTheta.modelDerivative t z)-
      (complexSlope t w-RiemannQuarticSaddleTheta.modelDerivative t w)‖ ≤
      32*‖z-w‖ := by
  have ha := slope_error_analytic_on_neighborhood t u hu
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (ha x (closedBall_subset_closedBall (by norm_num) hx)).differentiableAt)
    (fun x hx => ?_) (convex_closedBall (u : ℂ) (1/32)) hw hz
  simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, pow_one, one_mul] using
    slope_error_inner_cauchy_bound t u hu x hx 1

theorem slope_error_deriv_inner_lipschitz (t u : ℝ) (hu : 1 ≤ u) (w z : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/32))
    (hz : z ∈ closedBall (u : ℂ) (1/32)) :
    ‖deriv (fun x => complexSlope t x-RiemannQuarticSaddleTheta.modelDerivative t x) z-
      deriv (fun x => complexSlope t x-RiemannQuarticSaddleTheta.modelDerivative t x) w‖ ≤
      2048*‖z-w‖ := by
  have ha := slope_error_analytic_on_neighborhood t u hu
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (ha x (closedBall_subset_closedBall (by norm_num) hx)).deriv.differentiableAt)
    (fun x hx => ?_) (convex_closedBall (u : ℂ) (1/32)) hw hz
  have h := slope_error_inner_cauchy_bound t u hu x hx 2
  norm_num [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] at h
  exact h


open RiemannQuarticCurvature RiemannQuarticSaddleTimes

theorem stationary_slope_norm_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    ‖complexSlope t w‖ ≤ 100*(t*u^3+1) := by
  have hu0 : 0 ≤ u := by linarith
  have hq : 0 ≤ t*u^3 := by positivity
  have hscale := stationary_scale_bounds t u hu hs
  have hnorm : ‖w‖ ≤ u+1 := by
    have h := norm_add_le (w-(u : ℂ)) (u : ℂ)
    have hd : ‖w-(u : ℂ)‖ ≤ (1/16 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg hu0] at h
    linarith
  have hc : ‖w‖^3 ≤ 8*u^3 := by
    calc
      _ ≤ (u+1)^3 := pow_le_pow_left₀ (norm_nonneg _) hnorm 3
      _ ≤ (2*u)^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = _ := by ring
  have he := exp_complex_norm_upper u w hw
  have hm : ‖RiemannQuarticSaddleTheta.modelDerivative t w‖ ≤
      32*(t*u^3)+9+(16/3)*Real.pi*Real.exp (4*u) := by
    unfold RiemannQuarticSaddleTheta.modelDerivative
    have h1 := norm_sub_le (4*(t : ℂ)*w^3+9) (4*(Real.pi : ℂ)*Complex.exp (4*w))
    have h2 := norm_add_le (4*(t : ℂ)*w^3) (9 : ℂ)
    norm_num only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg ht,abs_of_pos Real.pi_pos] at h1 h2
    have hp := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 4*t)
    have hpe := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4*Real.pi)
    nlinarith
  have htriangle := norm_add_le
    (complexSlope t w-RiemannQuarticSaddleTheta.modelDerivative t w)
    (RiemannQuarticSaddleTheta.modelDerivative t w)
  rw [sub_add_cancel] at htriangle
  have herr := slope_model_error_on_neighborhood t u hu w hw
  nlinarith

theorem stationary_slope_inner_cauchy_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/32)) (n : ℕ) :
    ‖iteratedDeriv n (complexSlope t) w‖ ≤ (n.factorial : ℝ)*(100*(t*u^3+1))*32^n := by
  have hsub := inner_neighborhood_subset u w hw
  have ha := (slope_analytic_on_neighborhood t u hu).mono hsub
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1/32)
    (ha.differentiableOn.diffContOnCl_ball (Set.Subset.refl _))
    (fun z hz => stationary_slope_norm_bound t u ht hu hs z
      (hsub (sphere_subset_closedBall hz)))
  calc
    _ ≤ (n.factorial : ℝ)*(100*(t*u^3+1))/((1/32 : ℝ)^n) := h
    _ = _ := by simp only [one_div,inv_pow,div_inv_eq_mul]

theorem stationary_slope_deriv_inner_lipschitz (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (w z : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/32)) (hz : z ∈ closedBall (u : ℂ) (1/32)) :
    ‖deriv (complexSlope t) z-deriv (complexSlope t) w‖ ≤
      (204800*(t*u^3+1))*‖z-w‖ := by
  have ha := slope_analytic_on_neighborhood t u hu
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (ha x (closedBall_subset_closedBall (by norm_num) hx)).deriv.differentiableAt)
    (fun x hx => ?_) (convex_closedBall (u : ℂ) (1/32)) hw hz
  have h := stationary_slope_inner_cauchy_bound t u ht hu hs x hx 2
  norm_num [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] at h
  convert h using 1 <;> ring

theorem stationary_slope_deriv_norm_lower (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) :
    4*(t*u^3+1) ≤ ‖deriv (complexSlope t) (u : ℂ)‖ := by
  have ha := complexSlope_analyticAt t u (by linarith)
  have hr : HasDerivAt (phaseSlope t) (deriv (complexSlope t) (u : ℂ)).re u := by
    convert ha.differentiableAt.hasDerivAt.real_of_complex using 1
    funext x
    rw [complexSlope_real]
    rfl
  have hc := stationary_curvature_bounds t u hu hs
  have hn := Complex.abs_re_le_norm (deriv (complexSlope t) (u : ℂ))
  have hp : 4*t*u^3 ≤ 4*t*u^2*(4*u-3) := by
    have h := mul_le_mul_of_nonneg_left (by linarith : u ≤ 4*u-3)
      (by positivity : 0 ≤ 4*t*u^2)
    nlinarith
  have hab := neg_le_abs ((deriv (complexSlope t) (u : ℂ)).re)
  rw [← hr.deriv] at hn hab
  linarith [hc.2]

theorem scalar_ball_surj (f : ℂ → ℂ) (b a : ℂ) (r : ℝ) (hr : 0 ≤ r) (ha : a ≠ 0)
    (hd : ∀ w ∈ closedBall b r, DifferentiableAt ℂ f w)
    (hb : ∀ w ∈ closedBall b r, ‖deriv f w-a‖ ≤ ‖a‖/2) :
    SurjOn f (closedBall b r) (closedBall (f b) (‖a‖*r/2)) := by
  let L : ℂ →L[ℂ] ℂ := a • ContinuousLinearMap.id ℂ ℂ
  let c : NNReal := ⟨‖a‖/2,by positivity⟩
  have happ : ApproximatesLinearOn f L (closedBall b r) c := by
    intro x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hd w hw).sub ((hasDerivAt_id w).const_mul a).differentiableAt)
      (fun w hw => by
        rw [deriv_sub (hd w hw) ((hasDerivAt_id w).const_mul a).differentiableAt,
          ((hasDerivAt_id w).const_mul a).deriv]
        simpa using hb w hw)
      (convex_closedBall b r) hy hx
    change ‖f x-f y-a*(x-y)‖ ≤ (‖a‖/2)*‖x-y‖
    simp only [Pi.sub_apply, id_eq] at h
    convert h using 1 <;> congr 1 <;> ring
  let inv : L.NonlinearRightInverse := {
    toFun := fun y => a⁻¹*y
    nnnorm := ‖a⁻¹‖₊
    bound' := fun y => by simp only [norm_mul, coe_nnnorm]; exact le_rfl
    right_inv' := fun y => by
      change a*(a⁻¹*y)=y
      rw [← mul_assoc,mul_inv_cancel₀ ha,one_mul] }
  have h := happ.surjOn_closedBall_of_nonlinearRightInverse inv hr (Subset.refl _)
  have he : ((inv.nnnorm : ℝ)⁻¹-(c : ℝ))*r=‖a‖*r/2 := by
    change (‖a⁻¹‖⁻¹-‖a‖/2)*r=‖a‖*r/2
    rw [norm_inv,inv_inv]
    ring
  rw [he] at h
  exact h


theorem scalar_ball_injective (f : ℂ → ℂ) (b a : ℂ) (r : ℝ) (ha : a ≠ 0)
    (hd : ∀ w ∈ closedBall b r, DifferentiableAt ℂ f w)
    (hb : ∀ w ∈ closedBall b r, ‖deriv f w-a‖ ≤ ‖a‖/2) :
    InjOn f (closedBall b r) := by
  intro x hx y hy heq
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hd w hw).sub ((hasDerivAt_id w).const_mul a).differentiableAt)
    (fun w hw => by
      rw [deriv_sub (hd w hw) ((hasDerivAt_id w).const_mul a).differentiableAt,
        ((hasDerivAt_id w).const_mul a).deriv]
      simpa using hb w hw)
    (convex_closedBall b r) hx hy
  simp only [Pi.sub_apply,id_eq] at h
  have he : f y-a*y-(f x-a*x)= -a*(y-x) := by rw [heq]; ring
  rw [he,norm_mul,norm_neg] at h
  have hp : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hn : ‖y-x‖=0 := by nlinarith [norm_nonneg (y-x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

theorem stationary_slope_deriv_near_center (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    ‖deriv (complexSlope t) w-deriv (complexSlope t) (u : ℂ)‖ ≤
      ‖deriv (complexSlope t) (u : ℂ)‖/2 := by
  have hw' : w ∈ closedBall (u : ℂ) (1/32) :=
    closedBall_subset_closedBall (by norm_num) hw
  have h := stationary_slope_deriv_inner_lipschitz t u ht hu hs (u : ℂ) w
    (by simp) hw'
  have hd : ‖w-(u : ℂ)‖ ≤ (1/102400 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hw
  have hq : 0 ≤ t*u^3+1 := by positivity
  have hp := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 204800*(t*u^3+1))
  have hl := stationary_slope_deriv_norm_lower t u ht hu hs
  nlinarith

theorem existsUnique_frequency_saddle (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (z : ℂ) (hz : ‖z‖ ≤ (t*u^3+1)/51200) :
    ∃! w, w ∈ closedBall (u : ℂ) (1/102400) ∧ complexSlope t w= -(Complex.I*z) := by
  let a := deriv (complexSlope t) (u : ℂ)
  have ha : a ≠ 0 := complexSlope_deriv_ne_zero_of_real t u (by linarith)
    (ne_of_lt (stationary_phaseSlope_deriv_neg t u ht hu hs))
  have hd : ∀ w ∈ closedBall (u : ℂ) (1/102400), DifferentiableAt ℂ (complexSlope t) w := by
    intro w hw
    exact (slope_analytic_on_neighborhood t u hu w
      (closedBall_subset_closedBall (by norm_num) hw)).differentiableAt
  have hb := stationary_slope_deriv_near_center t u ht hu hs
  have hsurj := scalar_ball_surj (complexSlope t) (u : ℂ) a (1/102400)
    (by norm_num) ha hd hb
  have hzero : complexSlope t (u : ℂ)=0 := by rw [complexSlope_real,hs,Complex.ofReal_zero]
  have hmem : -(Complex.I*z) ∈ closedBall (complexSlope t (u : ℂ)) (‖a‖*(1/102400)/2) := by
    rw [hzero,mem_closedBall,dist_zero_right,norm_neg,norm_mul,Complex.norm_I,one_mul]
    have hl := stationary_slope_deriv_norm_lower t u ht hu hs
    change 4*(t*u^3+1) ≤ ‖a‖ at hl
    linarith
  obtain ⟨w,hw,he⟩ := hsurj hmem
  refine ⟨w,⟨hw,he⟩,?_⟩
  intro v hv
  exact scalar_ball_injective (complexSlope t) (u : ℂ) a (1/102400) ha hd hb hv.1 hw
    (hv.2.trans he.symm)


theorem frequency_saddle_domain (_t u : ℝ) (hu : 1 ≤ u) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    0 < (Complex.exp (4*w)).re ∧ RiemannThetaComplexKernel.kernelComplex w ≠ 0 := by
  have hw' : w ∈ closedBall (u : ℂ) (1/16) :=
    closedBall_subset_closedBall (by norm_num) hw
  exact ⟨by linarith [(neighborhood_domain u hu w hw').2],
    kernel_nonzero_on_neighborhood u hu w hw'⟩

theorem frequency_saddle_deriv_ne_zero (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/102400)) : deriv (complexSlope t) w ≠ 0 := by
  have h := stationary_slope_deriv_near_center t u ht hu hs w hw
  have hl := stationary_slope_deriv_norm_lower t u ht hu hs
  intro he
  rw [he,zero_sub,norm_neg] at h
  have hq : 0 ≤ t*u^3 := by positivity
  linarith

theorem eventually_all_maxima_frequency_disk :
    ∀ᶠ t : ℝ in Filter.atTop, ∀ u ∈ Set.Ici (0 : ℝ),
      IsMaxOn (RiemannQuarticDomain.weighted 0 t 0) (Set.Ici 0) u →
      ∀ z : ℂ, ‖z‖ ≤ (t+1)/51200 →
        ∃! w, w ∈ closedBall (u : ℂ) (1/102400) ∧ complexSlope t w= -(Complex.I*z) := by
  filter_upwards [RiemannQuarticRealSaddle.maxima_escape 1 (by norm_num),
    Filter.eventually_ge_atTop (0 : ℝ)] with t he ht
  intro u hu hm z hz
  have hu1 : 1 ≤ u := (he u hu hm).le
  have hs := RiemannQuarticRealSaddle.max_real_stationary t u (by linarith) hm
  rw [← (RiemannQuarticRealSaddle.kernel_hasDerivAt u).deriv] at hs
  apply existsUnique_frequency_saddle t u ht hu1 hs z
  have hp : 1 ≤ u^3 := by nlinarith [sq_nonneg (u-1),mul_nonneg (sub_nonneg.mpr hu1) (sq_nonneg u)]
  have hmul := mul_le_mul_of_nonneg_left hp ht
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticQuantitativeSaddle
