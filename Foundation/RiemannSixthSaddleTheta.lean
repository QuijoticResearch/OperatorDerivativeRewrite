import Foundation.RiemannEvenModelPhase
import Foundation.RiemannQuarticFarModelSaddle

/-! The sixth-order model's actual arithmetic domain and theta control.
An exact model saddle is still not asserted to be an actual saddle. -/
noncomputable section
open Set Complex
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthSaddleTheta
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannThetaComplexKernel

theorem fifth_power_re (w : ℂ) :
    (w^5).re = w.re^5-10*w.re^3*w.im^2+5*w.re*w.im^4 := by
  simp only [pow_succ,pow_zero,one_mul,Complex.mul_re,Complex.mul_im]
  ring

theorem model_real_identity (t : ℝ) (z w : ℂ)
    (hs : modelDerivative 3 t w = -(Complex.I*z)) :
    4*Real.pi*(Complex.exp (4*w)).re =
      6*t*(w.re^5-10*w.re^3*w.im^2+5*w.re*w.im^4)+9-z.im := by
  have h := congrArg Complex.re hs
  norm_num [modelDerivative,Complex.mul_re,fifth_power_re] at h
  linarith

theorem model_real_margin (t : ℝ) (z w : ℂ) (ht : 0 ≤ t)
    (hr : 2 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w = -(Complex.I*z)) :
    t*w.re^5+9-z.im ≤ 4*Real.pi*(Complex.exp (4*w)).re := by
  have hr0 : 0 ≤ w.re := by linarith
  have hr2 : 4 ≤ w.re^2 := by nlinarith
  have hr3 : 0 ≤ w.re^3 := by positivity
  have hr5 : 4*w.re^3 ≤ w.re^5 := by
    have h := mul_le_mul_of_nonneg_right hr2 hr3
    nlinarith
  have hib : w.im^2 ≤ 1/4 := by
    rcases abs_le.mp hi with ⟨hl,hh⟩
    nlinarith [sq_nonneg w.im]
  have hbad := mul_le_mul_of_nonneg_left hib (show 0 ≤ 60*w.re^3 by positivity)
  have hgood : 0 ≤ 30*w.re*w.im^4 := by positivity
  have hpoly : w.re^5 ≤ 6*(w.re^5-10*w.re^3*w.im^2+5*w.re*w.im^4) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hpoly ht
  rw [model_real_identity t z w hs]
  nlinarith

theorem kernel_nonzero_at_model (t : ℝ) (z w : ℂ) (ht : 0 ≤ t)
    (hr : 2 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w = -(Complex.I*z)) (hscale : 7 ≤ t*w.re^5-z.im) :
    kernelComplex w ≠ 0 := by
  apply RiemannThetaComplexKernel.kernel_ne_zero w (by linarith)
  have hm := model_real_margin t z w ht hr hi hs
  have hR : (16/(4*Real.pi) : ℝ) ≤ (Complex.exp (4*w)).re := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    linarith
  have h1 : (1 : ℝ) ≤ 16/(4*Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    linarith [Real.pi_lt_four]
  exact h1.trans hR

theorem theta_tail_at_model (t : ℝ) (z w : ℂ) (ht : 0 ≤ t)
    (hz : z.im ≤ 0) (hr : 2 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w = -(Complex.I*z)) (k : ℕ) (hk : k ≤ 4) :
    ‖RiemannQuarticSaddleTheta.complexThetaTail k 1 (Complex.exp (4*w))‖ ≤
      32*Real.exp (-(3/4 : ℝ)*(t*w.re^5+9-z.im))*
        ‖RiemannQuarticSaddleTheta.complexThetaTerm k (Complex.exp (4*w)) 0‖ := by
  have hm := model_real_margin t z w ht hr hi hs
  have hp : 0 ≤ t*w.re^5 := by positivity
  have hR : (9/(4*Real.pi) : ℝ) ≤ (Complex.exp (4*w)).re := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    linarith
  have hhalf : (1/2 : ℝ) ≤ 9/(4*Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    linarith [Real.pi_lt_four]
  have he : Real.exp (-3*Real.pi*(Complex.exp (4*w)).re) ≤
      Real.exp (-(3/4 : ℝ)*(t*w.re^5+9-z.im)) := Real.exp_le_exp.mpr (by nlinarith)
  exact (RiemannQuarticSaddleTheta.complexThetaTail_relative k hk (Complex.exp (4*w)) (hhalf.trans hR)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) (norm_nonneg _))

theorem actual_slope_residual_at_model (t x : ℝ) (w : ℂ) (ht : 1 ≤ t)
    (hr : 4 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w = -(Complex.I*(x : ℂ))) :
    ‖complexSlope 3 t w+Complex.I*(x : ℂ)‖ ≤ 30005*Real.exp (-w.re) := by
  have hm := model_real_margin t (x : ℂ) w (by linarith) (by linarith) hi hs
  simp only [Complex.ofReal_im,sub_zero] at hm
  have hp : 1 ≤ w.re^5 := one_le_pow₀ (by linarith : 1 ≤ w.re)
  have hR : 1 ≤ (Complex.exp (4*w)).re := by
    have hlarge : 0 ≤ t*w.re^5 := by positivity
    have hpoly : 4*Real.pi ≤ t*w.re^5+9 := by
      have hr5 : (1024 : ℝ) ≤ w.re^5 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hr 5
        norm_num at h
        exact h
      have htr := mul_le_mul_of_nonneg_right ht (pow_nonneg (by linarith : 0 ≤ w.re) 5)
      nlinarith [Real.pi_lt_four]
    nlinarith [Real.pi_pos]
  have hid : complexSlope 3 t w+Complex.I*(x : ℂ) =
      kernelDerivative w/kernelComplex w-(9-4*(Real.pi : ℂ)*Complex.exp (4*w)) := by
    have hactual := (kernelComplex_hasDerivAt w (by linarith : 0 < (Complex.exp (4*w)).re)).deriv
    unfold complexSlope modelDerivative at *
    rw [hactual]
    norm_num at hs ⊢
    linear_combination hs
  rw [hid]
  have hb := RiemannQuarticSaddleNeighborhood.logDerivative_coarse_bound w (by linarith) hR
  have he : Real.exp (-3*Real.pi*(Complex.exp (4*w)).re) ≤
      Real.exp (-(3/4 : ℝ)*(t*w.re^5+9)) := Real.exp_le_exp.mpr (by nlinarith)
  have h35 : w.re^3 ≤ w.re^5 := pow_le_pow_right₀ (by linarith : 1 ≤ w.re) (by norm_num)
  have he3 : Real.exp (-(3/4 : ℝ)*(t*w.re^5+9)) ≤ Real.exp (-(3/4 : ℝ)*(t*w.re^3+9)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left h35 (by linarith : 0 ≤ t)
    linarith
  have hterm := mul_le_mul_of_nonneg_left (he.trans he3)
    (show 0 ≤ 30000*Real.exp (4*w.re) by positivity)
  have henv := RiemannQuarticFarModelSaddle.scalar_residual_envelope t w.re ht hr
  nlinarith

end OperatorDerivativeRewrite.Foundation.RiemannSixthSaddleTheta
