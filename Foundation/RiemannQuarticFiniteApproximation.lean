import Foundation.RiemannThetaTruncation
import Foundation.RiemannQuarticJetCutoff

/-! A finite elementary integral approximates the actual arithmetic flow jets.
The estimate does not certify any numerical quadrature or zero location. -/
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFiniteApproximation
open RiemannQuarticKernel RiemannQuarticDomain RiemannQuarticFlow
open RiemannQuarticEvolution RiemannThetaTruncation RiemannQuarticJetCutoff

def partialIntegrand (N k : ℕ) (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (Real.exp (t*u^4)*partialKernel N u : ℂ)*
    (Complex.I*(u : ℂ))^k*Complex.exp (Complex.I*(u : ℂ)*z)

theorem partialIntegrand_continuous (N k : ℕ) (t : ℝ) (z : ℂ) :
    Continuous (partialIntegrand N k t z) := by
  unfold partialIntegrand
  have hc := partialKernel_continuous N
  fun_prop

theorem integrand_difference_norm (N k : ℕ) (t x u : ℝ) (hu : 0 ≤ u) :
    ‖integrand k t (x : ℂ) u-partialIntegrand N k t (x : ℂ) u‖ =
      |u^k*Real.exp (t*u^4)*(kernel u-partialKernel N u)| := by
  have hp : ‖Complex.exp (Complex.I*(u : ℂ)*(x : ℂ))‖=1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  have he : integrand k t (x : ℂ) u-partialIntegrand N k t (x : ℂ) u =
      (Real.exp (t*u^4)*(kernel u-partialKernel N u) : ℂ)*
        (Complex.I*(u : ℂ))^k*Complex.exp (Complex.I*(u : ℂ)*(x : ℂ)) := by
    simp only [integrand, partialIntegrand, weighted, pow_zero, one_mul,
      zero_mul, add_zero, Complex.ofReal_mul]
    ring
  rw [he]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, one_mul, abs_of_nonneg hu, hp, mul_one, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_nonneg (pow_nonneg hu k)]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  ring

def finiteJet (N k : ℕ) (t : ℝ) (z : ℂ) (R : ℝ) : ℂ :=
  ∫ u in 0..R, partialIntegrand N k t z u

theorem cutoff_finite_error (k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    ‖cutoffJet k 8 (x : ℂ) (8/5)-finiteJet 15 k 8 (x : ℂ) (8/5)‖ ≤
      (8/5 : ℝ)*(1/10^100) := by
  have hi : IntervalIntegrable (integrand k 8 (x : ℂ)) volume 0 (8/5) := by
    apply ContinuousOn.intervalIntegrable
    apply (integrand_continuousOn k 8 (x : ℂ)).mono
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 8/5)]
    exact fun u hu => hu.1
  have hj := (partialIntegrand_continuous 15 k 8 (x : ℂ)).intervalIntegrable
    (μ := volume) (a := (0 : ℝ)) (b := (8/5 : ℝ))
  rw [cutoffJet, finiteJet, ← intervalIntegral.integral_sub hi hj]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (8/5 : ℝ)) (C := (1/10^100 : ℝ))
    (f := fun u => integrand k 8 (x : ℂ) u-partialIntegrand 15 k 8 (x : ℂ) u) (by
      intro u hu
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 8/5)] at hu
      rw [integrand_difference_norm 15 k 8 x u (le_of_lt hu.1)]
      exact fifteen_term_remainder k hk u (le_of_lt hu.1) hu.2)
  norm_num only [sub_zero, abs_of_pos (by norm_num : (0 : ℝ) < 8/5)] at h
  convert h using 1 <;> norm_num

theorem jet_finite_error (k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    ‖jet k 8 (x : ℂ)-finiteJet 15 k 8 (x : ℂ) (8/5)‖ ≤ (1/10^27 : ℝ) := by
  have h := dist_triangle (jet k 8 (x : ℂ)) (cutoffJet k 8 (x : ℂ) (8/5))
    (finiteJet 15 k 8 (x : ℂ) (8/5))
  simp only [dist_eq_norm] at h
  have ht := jet_cutoff_error k hk x
  have hf := cutoff_finite_error k hk x
  linarith

def finiteDerivative (N k : ℕ) (t : ℝ) (z : ℂ) (R : ℝ) : ℂ :=
  (finiteJet N k t z R+(-1 : ℂ)^k*finiteJet N k t (-z) R)/2

theorem derivative_finite_error (k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    ‖iteratedDeriv k (flow 8) (x : ℂ)-finiteDerivative 15 k 8 (x : ℂ) (8/5)‖ ≤
      (1/10^27 : ℝ) := by
  rw [flow_iteratedDeriv]
  have hp := jet_finite_error k hk x
  have hm := jet_finite_error k hk (-x)
  simp only [Complex.ofReal_neg] at hm
  have he : symmetricJet k 8 (x : ℂ)-finiteDerivative 15 k 8 (x : ℂ) (8/5) =
      ((jet k 8 (x : ℂ)-finiteJet 15 k 8 (x : ℂ) (8/5))+
        (-1 : ℂ)^k*(jet k 8 (-(x : ℂ))-finiteJet 15 k 8 (-(x : ℂ)) (8/5)))/2 := by
    unfold symmetricJet finiteDerivative
    ring
  rw [he, norm_div]
  have hn : ‖(-1 : ℂ)^k‖=1 := by simp
  have h := norm_add_le (jet k 8 (x : ℂ)-finiteJet 15 k 8 (x : ℂ) (8/5))
    ((-1 : ℂ)^k*(jet k 8 (-(x : ℂ))-finiteJet 15 k 8 (-(x : ℂ)) (8/5)))
  rw [norm_mul, hn, one_mul] at h
  norm_num only [Complex.norm_ofNat] at *
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFiniteApproximation
