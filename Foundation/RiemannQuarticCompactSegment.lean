import Foundation.RiemannQuarticDistantTail
import Foundation.RiemannQuarticEndpointSaddle
/-! Actual compact shifted-segment bounds for the quartic Xi integrand.
The interval [0,1] has signed integral norm <=5676*exp(16*abs(t)+2*norm(z)+9).
Using an actual global amplitude maximum and the existing actual branch weight
lower bound, norm(z)<=t gives relative error <=5676/Phi(3)*exp(10-503*t/8).
All branch, phase remainder and frequency-region assumptions are retained. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCompactSegment
open RiemannQuarticFrequencyBranch RiemannQuarticContour RiemannQuarticSaddleNeighborhood
open RiemannThetaComplexKernel RiemannQuarticSaddleBranch RiemannQuarticSaddleTimes
open RiemannQuarticEndpointSaddle RiemannQuarticDomain RiemannQuarticKernel RiemannQuarticRealSaddle

theorem compact_weight_norm (t : ℝ) (z : ℂ) (x h : ℝ) (hx : x ∈ Icc 0 1) (hh : |h| ≤ 1/16) :
    ‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      5676*Real.exp (16*|t|+2*‖z‖+9) := by
  let w := (x : ℂ)+(h : ℂ)*Complex.I
  have hwre : w.re=x := by simp [w]
  have hwim : w.im=h := by simp [w]
  have hk := kernel_strip_norm_bound w (by simpa [hwre] using hx.1) (by simpa [hwim] using hh)
  have hk' : ‖kernelComplex w‖ ≤ 5676*Real.exp 9 := by
    have he1 : Real.exp (9*w.re) ≤ Real.exp 9 := Real.exp_le_exp.mpr (by rw [hwre]; linarith [hx.2])
    have he2 : Real.exp (-(Real.pi/2)*Real.exp (4*w.re)) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) (Real.exp_pos _).le)
    calc
      _ ≤ 5676*Real.exp (9*w.re)*Real.exp (-(Real.pi/2)*Real.exp (4*w.re)) := hk
      _ ≤ 5676*Real.exp 9*1 := mul_le_mul (by gcongr) he2 (by positivity) (by positivity)
      _ = _ := mul_one _
  have hn := norm_add_le (x : ℂ) ((h : ℂ)*Complex.I)
  simp only [Complex.norm_real,Real.norm_eq_abs,norm_mul,Complex.norm_I,mul_one,abs_of_nonneg hx.1] at hn
  have hw : ‖w‖ ≤ 2 := by dsimp [w]; linarith [hx.2]
  have hp : ‖w‖^4 ≤ 16 := by
    calc
      _ ≤ (2 : ℝ)^4 := pow_le_pow_left₀ (norm_nonneg w) hw 4
      _ = _ := by norm_num
  have hre := Complex.re_le_norm ((t : ℂ)*w^4+Complex.I*z*w)
  have htri := norm_add_le ((t : ℂ)*w^4) (Complex.I*z*w)
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,one_mul] at htri
  have h1 := mul_le_mul_of_nonneg_left hp (abs_nonneg t)
  have h2 := mul_le_mul_of_nonneg_left hw (norm_nonneg z)
  have he : ((t : ℂ)*w^4+Complex.I*z*w).re ≤ 16*|t|+2*‖z‖ := by nlinarith
  change ‖saddleWeight t z w‖ ≤ _
  rw [saddleWeight,norm_mul,Complex.norm_exp]
  calc
    _ ≤ Real.exp (16*|t|+2*‖z‖)*(5676*Real.exp 9) :=
      mul_le_mul (Real.exp_le_exp.mpr he) hk' (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [mul_comm _ (5676*Real.exp 9),mul_assoc,← Real.exp_add]; congr 2 <;> ring

theorem compact_signed_integral_bound (t : ℝ) (z : ℂ) (h : ℝ) (hh : |h| ≤ 1/16) :
    ‖∫ x : ℝ in 0..1, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      5676*Real.exp (16*|t|+2*‖z‖+9) := by
  have hg : IntervalIntegrable (fun _ : ℝ => 5676*Real.exp (16*|t|+2*‖z‖+9)) volume 0 1 := intervalIntegrable_const
  have hb := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1)
    (Eventually.of_forall (fun x hx => compact_weight_norm t z x h ⟨hx.1.le,hx.2⟩ hh)) hg
  simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using hb

theorem compact_relative_saddle_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) (him : z.im ≤ 0) (hzt : ‖z‖ ≤ t)
    (hsmall : (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1) (hregion : ‖z‖^2 ≤ t*(t*u^3+1))
    (h : ℝ) (hh : |h| ≤ 1/16) :
    ‖∫ x : ℝ in 0..1, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖/
      ‖saddleWeight t z (branch t u ht hu hs z)‖ ≤
      (5676/kernel 3)*Real.exp (10-503*t/8) := by
  have hpeak := hm (by norm_num : (3 : ℝ) ∈ Ici 0)
  change weighted 0 t 0 3 ≤ weighted 0 t 0 u at hpeak
  have hpeak' : Real.exp (81*t)*kernel 3 ≤ weighted 0 t 0 u := by
    have hthree : weighted 0 t 0 3=Real.exp (81*t)*kernel 3 := by
      simp only [weighted,pow_zero,one_mul,zero_mul,add_zero,show (3 : ℝ)^4=81 by norm_num]
      rw [mul_comm t 81]
    rw [hthree] at hpeak
    exact hpeak
  have hA := dominant_weight_norm_lower t u ht hu hs z hz him hsmall hregion
  have hA' : (Real.exp (81*t)*kernel 3)*Real.exp (-t/8-1) ≤
      ‖saddleWeight t z (branch t u ht hu hs z)‖ :=
    (mul_le_mul_of_nonneg_right hpeak' (Real.exp_pos _).le).trans hA
  have hK := kernel_pos 3 (by norm_num)
  have hden : 0 < (Real.exp (81*t)*kernel 3)*Real.exp (-t/8-1) := by positivity
  have hnum := compact_signed_integral_bound t z h hh
  rw [abs_of_nonneg ht] at hnum
  have hnum' : ‖∫ x : ℝ in 0..1, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      5676*Real.exp (18*t+9) :=
    hnum.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  calc
    _ ≤ (5676*Real.exp (18*t+9))/‖saddleWeight t z (branch t u ht hu hs z)‖ :=
      div_le_div_of_nonneg_right hnum' (lt_of_lt_of_le hden hA').le
    _ ≤ (5676*Real.exp (18*t+9))/((Real.exp (81*t)*kernel 3)*Real.exp (-t/8-1)) :=
      div_le_div_of_nonneg_left (by positivity) hden hA'
    _ = _ := by
      apply (div_eq_iff hden.ne').mpr
      have he : Real.exp (10-503*t/8)*Real.exp (81*t)*Real.exp (-t/8-1)=Real.exp (18*t+9) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      rw [← he]
      have hc : (5676/kernel 3)*kernel 3=5676 := div_mul_cancel₀ _ hK.ne'
      calc
        _ = ((5676/kernel 3)*kernel 3)*
            (Real.exp (10-503*t/8)*Real.exp (81*t)*Real.exp (-t/8-1)) := by rw [hc]
        _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCompactSegment
