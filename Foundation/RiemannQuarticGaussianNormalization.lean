import Foundation.RiemannQuarticDistantTail
/-! Quantitative lower normalization for the actual-curvature Gaussian model.
Its coefficient norm is <=1600Q. The exact Gaussian integral-square identity
then gives 1<=40*sqrt(Q)*norm(Gfull), Q=t*u^3+1. This supports relative-error
estimates; the Gaussian model is not identified with the full Fourier integral. -/
noncomputable section
open Set Metric Complex MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticGaussianNormalization
open RiemannQuarticSaddleBranch RiemannQuarticSaddleTimes RiemannQuarticQuantitativeSaddle
open RiemannQuarticSaddleGeometry RiemannQuarticGaussianTail

theorem coefficient_norm_upper (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    ‖-(deriv (complexSlope t) w)/2‖ ≤ 1600*(t*u^3+1) := by
  have h := stationary_slope_inner_cauchy_bound t u ht hu hs w
    (closedBall_subset_closedBall (by norm_num : (1/102400 : ℝ)≤1/32) hw) 1
  simp only [iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,pow_one,one_mul] at h
  rw [norm_div,norm_neg,Complex.norm_ofNat]
  linarith

theorem gaussian_norm_sq (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    ‖((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ)‖^2=
      Real.pi/‖-(deriv (complexSlope t) w)/2‖ := by
  have hc := gaussian_coefficient_re_pos t u ht hu hs w hw
  have hg := integral_gaussian_sq_complex hc
  have hident : (fun s : ℝ => Complex.exp (-(-(deriv (complexSlope t) w)/2)*(s : ℂ)^2))=
      (fun s : ℝ => Complex.exp ((deriv (complexSlope t) w/2)*(s : ℂ)^2)) := by
    funext s
    congr 1
    ring
  rw [hident,quadratic_gaussian_integral t u ht hu hs w hw] at hg
  have hn := congrArg norm hg
  simpa only [norm_pow,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos] using hn

theorem gaussian_norm_lower (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    1 ≤ 40*Real.sqrt (t*u^3+1)*‖((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ)‖ := by
  let Q := t*u^3+1
  let g := ‖((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ)‖
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hg0 : 0 ≤ g := norm_nonneg _
  have hc := coefficient_norm_upper t u ht hu hs w hw
  have hnormpos : 0 < ‖-(deriv (complexSlope t) w)/2‖ := norm_pos_iff.mpr
    (by intro he; have hp := gaussian_coefficient_re_pos t u ht hu hs w hw; rw [he] at hp; simp at hp)
  have hsq := gaussian_norm_sq t u ht hu hs w hw
  have hid : g^2*‖-(deriv (complexSlope t) w)/2‖=Real.pi := by
    exact (eq_div_iff hnormpos.ne').mp hsq
  have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg g)
  have hroot := Real.sq_sqrt hQ.le
  have hprod : 0 ≤ 40*Real.sqrt Q*g := by positivity
  have hsquare : 1 ≤ (40*Real.sqrt Q*g)^2 := by
    calc
      _ ≤ Real.pi := (by linarith [Real.pi_gt_three])
      _ ≤ g^2*(1600*Q) := by nlinarith [hid,hm]
      _ = _ := by rw [mul_pow,mul_pow,hroot]; ring
  change 1 ≤ 40*Real.sqrt Q*g
  nlinarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticGaussianNormalization
