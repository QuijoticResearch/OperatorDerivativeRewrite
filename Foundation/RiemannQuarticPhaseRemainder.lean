import Foundation.RiemannQuarticFrequencyBranch
/-! Actual saddle phase Taylor remainder and complex relative weight error.
The normalized phase P satisfies a quadratic remainder <=25600*norm(z)^3/Q^2.
The actual saddle weight divided by its quadratic-exponential approximation
has error <=51200*norm(z)^3/Q^2 when the phase error bound is <=1.
These estimates do not include the Gaussian prefactor or Fourier integral. -/
noncomputable section
open Set Metric
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticPhaseRemainder

theorem cubic_remainder_bound (f : ℂ → ℂ) (R M : ℝ) (hM : 0 ≤ M)
    (ha : AnalyticOnNhd ℂ f (ball 0 R))
    (h3 : ∀ w ∈ ball (0 : ℂ) R, ‖iteratedDeriv 3 f w‖ ≤ M)
    (z : ℂ) (hz : ‖z‖ < R) :
    ‖f z-f 0-deriv f 0*z-deriv (deriv f) 0*z^2/2‖ ≤ M*‖z‖^3 := by
  let r := ‖z‖
  have hr : 0 ≤ r := norm_nonneg z
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 R := by
    intro w hw
    have hw' : ‖w‖ ≤ r := by simpa using hw
    simpa using lt_of_le_of_lt hw' hz
  have hzero : (0 : ℂ) ∈ closedBall (0 : ℂ) r := mem_closedBall_self hr
  have hnorm (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) r) : ‖w‖ ≤ r := by simpa using hw
  have hsecond (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) r) :
      ‖deriv (deriv f) w-deriv (deriv f) 0‖ ≤ M*r := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun v hv => (ha v (hsub hv)).deriv.deriv.differentiableAt)
      (fun v hv => by simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using h3 v (hsub hv))
      (convex_closedBall (0 : ℂ) r) hzero hw
    simp only [sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hnorm w hw) hM)
  let H := fun w => deriv f w-deriv f 0-deriv (deriv f) 0*w
  have hHd (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) r) :
      HasDerivAt H (deriv (deriv f) w-deriv (deriv f) 0) w := by
    have h := (((ha w (hsub hw)).deriv.differentiableAt.hasDerivAt).sub_const (deriv f 0)).sub
      ((hasDerivAt_id w).const_mul (deriv (deriv f) 0))
    convert h using 1
    · funext v
      rfl
    · simp only [mul_one]
  have hfirst (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) r) : ‖H w‖ ≤ M*r*r := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun v hv => (hHd v hv).differentiableAt)
      (fun v hv => by rw [(hHd v hv).deriv]; exact hsecond v hv)
      (convex_closedBall (0 : ℂ) r) hzero hw
    have hH0 : H 0=0 := by simp [H]
    rw [hH0,sub_zero,sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hnorm w hw) (mul_nonneg hM hr))
  let T := fun w => f w-f 0-deriv f 0*w-deriv (deriv f) 0*w^2/2
  have hTd (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) r) : HasDerivAt T (H w) w := by
    have h := (((ha w (hsub hw)).differentiableAt.hasDerivAt.sub_const (f 0)).sub
      ((hasDerivAt_id w).const_mul (deriv f 0))).sub
      ((((hasDerivAt_id w).pow 2).const_mul (deriv (deriv f) 0)).div_const 2)
    convert h using 1
    · rfl
    · dsimp [H]
      ring
  have hzclosed : z ∈ closedBall (0 : ℂ) r := by simp [mem_closedBall,dist_zero_right,r]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun v hv => (hTd v hv).differentiableAt)
    (fun v hv => by rw [(hTd v hv).deriv]; exact hfirst v hv)
    (convex_closedBall (0 : ℂ) r) hzero hzclosed
  have hT0 : T 0=0 := by simp [T]
  rw [hT0,sub_zero,sub_zero] at h
  change ‖T z‖ ≤ M*‖z‖^3
  calc
    _ ≤ M*r*r*‖z‖ := h
    _ = _ := by dsimp [r]; ring

open RiemannQuarticFrequencyBranch RiemannQuarticSaddleBranch RiemannQuarticSaddleTimes

theorem phase_quadratic_remainder (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (P : ℂ → ℂ) (hP0 : P 0=0)
    (hP : ∀ z ∈ ball (0 : ℂ) ((t*u^3+1)/51200), HasDerivAt P (Complex.I*branch t u ht hu hs z) z)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) :
    ‖P z-Complex.I*(u : ℂ)*z-z^2/(2*deriv (complexSlope t) (u : ℂ))‖ ≤
      (25600/(t*u^3+1)^2)*‖z‖^3 := by
  have hpa : AnalyticOnNhd ℂ P (ball (0 : ℂ) ((t*u^3+1)/51200)) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    intro w hw
    exact (hP w hw).differentiableAt.differentiableWithinAt
  have h := cubic_remainder_bound P ((t*u^3+1)/51200) (25600/(t*u^3+1)^2)
    (by positivity) hpa (fun w hw => phase_third_deriv_norm_bound t u ht hu hs P hP w (by simpa using hw)) z hz
  have hr : 0 < (t*u^3+1)/51200 := by positivity
  have h0 : deriv P 0=Complex.I*(u : ℂ) := by rw [(hP 0 (mem_ball_self hr)).deriv,branch_zero]
  have h00 : deriv (deriv P) 0=(deriv (complexSlope t) (u : ℂ))⁻¹ := by
    have h := (phase_hasSecondDerivAt t u ht hu hs P hP 0 (by simpa using hr)).deriv
    simpa only [branch_zero] using h
  rw [hP0,h0,h00,sub_zero] at h
  convert h using 1 <;> congr 1 <;> ring


def quadraticSaddleWeight (t u : ℝ) (z : ℂ) : ℂ :=
  saddleWeight t 0 (u : ℂ)*Complex.exp (Complex.I*(u : ℂ)*z+z^2/(2*deriv (complexSlope t) (u : ℂ)))

theorem zero_saddleWeight_ne_zero (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0) :
    saddleWeight t 0 (u : ℂ) ≠ 0 := by
  have hz : ‖(0 : ℂ)‖ ≤ (t*u^3+1)/51200 := by simp only [norm_zero]; positivity
  simpa only [branch_zero] using saddleWeight_ne_zero t u ht hu hs 0 hz

theorem quadraticSaddleWeight_ne_zero (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) : quadraticSaddleWeight t u z ≠ 0 :=
  mul_ne_zero (zero_saddleWeight_ne_zero t u ht hu hs) (Complex.exp_ne_zero _)

theorem saddleWeight_relative_quadratic_error (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200)
    (hsmall : (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1) :
    ‖saddleWeight t z (branch t u ht hu hs z)/quadraticSaddleWeight t u z-1‖ ≤
      (51200/(t*u^3+1)^2)*‖z‖^3 := by
  obtain ⟨P,hP0,hP⟩ := exists_normalized_phase t u ht hu hs
  let q := Complex.I*(u : ℂ)*z+z^2/(2*deriv (complexSlope t) (u : ℂ))
  have hrem : ‖P z-q‖ ≤ (25600/(t*u^3+1)^2)*‖z‖^3 := by
    have h := phase_quadratic_remainder t u ht hu hs P hP0 hP z hz
    convert h using 1 <;> congr 1 <;> dsimp [q] <;> ring
  have heq : saddleWeight t z (branch t u ht hu hs z)/quadraticSaddleWeight t u z=
      Complex.exp (P z-q) := by
    rw [saddleWeight_eq_exp_phase t u ht hu hs P hP0 hP z hz]
    change (saddleWeight t 0 (u : ℂ)*Complex.exp (P z))/
      (saddleWeight t 0 (u : ℂ)*Complex.exp q)=Complex.exp (P z-q)
    rw [mul_div_mul_left _ _ (zero_saddleWeight_ne_zero t u ht hu hs),Complex.exp_sub]
  rw [heq]
  have he := Complex.norm_exp_sub_one_le (hrem.trans hsmall)
  calc
    _ ≤ 2*‖P z-q‖ := he
    _ ≤ 2*((25600/(t*u^3+1)^2)*‖z‖^3) := mul_le_mul_of_nonneg_left hrem (by norm_num)
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticPhaseRemainder
