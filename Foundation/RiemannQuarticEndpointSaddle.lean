import Foundation.RiemannQuarticContour
import Foundation.RiemannQuarticPhaseRemainder
/-! Endpoint error relative to the actual frequency-dependent saddle weight.
For Re(z)>=0, Im(z)<=0, norm(z)<Q/51200, 25600*norm(z)^3/Q^2<=1
and norm(z)^2<=t*Q, the endpoint/actual saddle-weight ratio is bounded by
5676/(16*Phi(1))*exp(1-3*t/8). Here Q=t*u^3+1 at an actual stationary
positive real global amplitude maximum, t>=0,u>=1. This does not include
the Gaussian prefactor or an integrated saddle/tail remainder. -/
noncomputable section
open Set Metric Complex MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticEndpointSaddle
open RiemannQuarticFrequencyBranch RiemannQuarticPhaseRemainder RiemannQuarticSaddleBranch
open RiemannQuarticQuantitativeSaddle RiemannQuarticSaddleTimes RiemannQuarticContour
open RiemannQuarticDomain RiemannQuarticKernel RiemannQuarticRealSaddle RiemannThetaComplexKernel

theorem zero_weight_norm (t u : ℝ) (hu : 0 ≤ u) :
    ‖saddleWeight t 0 (u : ℂ)‖=weighted 0 t 0 u := by
  have he : saddleWeight t 0 (u : ℂ)=(weighted 0 t 0 u : ℂ) := by
    simp only [saddleWeight,weighted,pow_zero,one_mul,mul_zero,zero_mul,add_zero,kernelComplex_real]
    push_cast
    rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weighted_pos t u hu)]

theorem quadratic_phase_real_lower (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (z : ℂ) (him : z.im ≤ 0) :
    -(‖z‖^2/(8*(t*u^3+1))) ≤
      (Complex.I*(u : ℂ)*z+z^2/(2*deriv (complexSlope t) (u : ℂ))).re := by
  have hQ : 0 < t*u^3+1 := by positivity
  have hl := stationary_slope_deriv_norm_lower t u ht hu hs
  have hn : ‖z^2/(2*deriv (complexSlope t) (u : ℂ))‖ ≤ ‖z‖^2/(8*(t*u^3+1)) := by
    rw [norm_div,norm_pow,norm_mul,Complex.norm_ofNat]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    linarith
  have hab := Complex.abs_re_le_norm (z^2/(2*deriv (complexSlope t) (u : ℂ)))
  have hneg := neg_le_abs (z^2/(2*deriv (complexSlope t) (u : ℂ))).re
  have hlinear : 0 ≤ (Complex.I*(u : ℂ)*z).re := by
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,mul_zero,zero_sub,mul_one,one_mul,add_zero,sub_zero]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (by linarith) him)
  rw [Complex.add_re]
  linarith

theorem dominant_weight_norm_lower (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200)
    (him : z.im ≤ 0) (hsmall : (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1)
    (hregion : ‖z‖^2 ≤ t*(t*u^3+1)) :
    weighted 0 t 0 u*Real.exp (-t/8-1) ≤ ‖saddleWeight t z (branch t u ht hu hs z)‖ := by
  obtain ⟨P,hP0,hP⟩ := exists_normalized_phase t u ht hu hs
  let q := Complex.I*(u : ℂ)*z+z^2/(2*deriv (complexSlope t) (u : ℂ))
  have hrem : ‖P z-q‖ ≤ (25600/(t*u^3+1)^2)*‖z‖^3 := by
    have h := phase_quadratic_remainder t u ht hu hs P hP0 hP z hz
    convert h using 1 <;> congr 1 <;> dsimp [q] <;> ring
  have hquad := quadratic_phase_real_lower t u ht hu hs z him
  have hab := Complex.abs_re_le_norm (P z-q)
  have hneg := neg_le_abs (P z-q).re
  simp only [Complex.sub_re] at hab hneg
  have hQ : 0 < t*u^3+1 := by positivity
  have hr : ‖z‖^2/(8*(t*u^3+1)) ≤ t/8 := by
    apply (div_le_iff₀ (by positivity : 0 < 8*(t*u^3+1))).mpr
    nlinarith
  have hphase : -t/8-1 ≤ (P z).re := by
    change -(‖z‖^2/(8*(t*u^3+1))) ≤ q.re at hquad
    linarith
  rw [saddleWeight_eq_exp_phase t u ht hu hs P hP0 hP z hz,norm_mul,Complex.norm_exp,
    zero_weight_norm t u (by linarith)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase) (weighted_pos t u (by linarith)).le

theorem left_segment_relative_saddle_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) (hre : 0 ≤ z.re) (him : z.im ≤ 0)
    (hsmall : (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1) (hregion : ‖z‖^2 ≤ t*(t*u^3+1))
    (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1/16) :
    ‖∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)‖/
      ‖saddleWeight t z (branch t u ht hu hs z)‖ ≤
      (5676/(16*kernel 1))*Real.exp (1-3*t/8) := by
  have hpeakpos := weighted_pos t u (by linarith)
  have hA := dominant_weight_norm_lower t u ht hu hs z hz him hsmall hregion
  have hApos : 0 < weighted 0 t 0 u*Real.exp (-t/8-1) := by positivity
  have hnormpos := lt_of_lt_of_le hApos hA
  have hleft := left_segment_relative_peak_bound t u ht (by linarith) hm z hre h hh hh1
  have hnum := (div_le_iff₀ hpeakpos).mp hleft
  have hK : 0 ≤ 5676/(16*kernel 1) := by positivity [kernel_pos 1 (by norm_num)]
  calc
    _ ≤ ((5676/(16*kernel 1))*Real.exp (-t/2)*weighted 0 t 0 u)/
        ‖saddleWeight t z (branch t u ht hu hs z)‖ :=
      div_le_div_of_nonneg_right hnum hnormpos.le
    _ ≤ ((5676/(16*kernel 1))*Real.exp (-t/2)*weighted 0 t 0 u)/
        (weighted 0 t 0 u*Real.exp (-t/8-1)) :=
      div_le_div_of_nonneg_left (by positivity) hApos hA
    _ = _ := by
      apply (div_eq_iff (ne_of_gt hApos)).mpr
      have he : Real.exp (1-3*t/8)*Real.exp (-t/8-1)=Real.exp (-t/2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← he]
      ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticEndpointSaddle
