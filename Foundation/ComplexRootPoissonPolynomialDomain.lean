import Foundation.ComplexRootPoissonTransform
import Mathlib.Algebra.Order.Ring.Pow

/-! Genuine compound-root integrability and mixture formulas for unbounded polynomial moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonPolynomialDomain
open ComplexFourthRootNoise ComplexFourthRootWalk ComplexRootPoissonGrowth

theorem terminal_norm_bound (n : ℕ) (a : ℝ) (ω : Sample n) :
    ‖terminal n a ω‖ ≤ (n : ℝ)*(2*|a|) := by
  calc
    _ ≤ ∑ i : Fin n, ‖increment n a i ω‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, 2*|a| := Finset.sum_le_sum
      (fun i _ => ComplexRootPoissonTransform.noise_norm_bound a (ω i))
    _ = _ := by simp

theorem terminal_geometric_bound (n : ℕ) (a : ℝ) (ω : Sample n) :
    ‖terminal n a ω‖ ≤ (1+2*|a|)^n := by
  apply (terminal_norm_bound n a ω).trans
  have hb := one_add_mul_le_pow (a := 2*|a|) (by have ha := abs_nonneg a; linarith) n
  linarith

theorem terminal_power_bound (n k : ℕ) (a : ℝ) (ω : Sample n) :
    ‖terminal n a ω‖^k ≤ ((1+2*|a|)^k)^n := by
  have he := pow_le_pow_left₀ (norm_nonneg _) (terminal_geometric_bound n a ω) k
  simpa only [← pow_mul, Nat.mul_comm n k] using he

theorem power_integrable (r : ℝ≥0) (a : ℝ) (k : ℕ) :
    Integrable (fun z : ℂ => z^k) (ComplexRootPoissonLaw.law r a) := by
  apply growth_integrable r a _ (by fun_prop) ((1+2*|a|)^k)
  intro n ω
  simpa only [norm_pow] using terminal_power_bound n k a ω

theorem norm_power_integrable (r : ℝ≥0) (a : ℝ) (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖^k) (ComplexRootPoissonLaw.law r a) := by
  simpa only [norm_pow] using (power_integrable r a k).norm

theorem power_mixture (r : ℝ≥0) (a : ℝ) (k : ℕ) :
    (∫ z : ℂ, z^k ∂ComplexRootPoissonLaw.law r a) =
      ∫ n, (∫ ω, (terminal n a ω)^k ∂probability n) ∂poissonMeasure r := by
  apply integral_growth r a _ (by fun_prop) ((1+2*|a|)^k)
  intro n ω
  simpa only [norm_pow] using terminal_power_bound n k a ω

theorem norm_power_mixture (r : ℝ≥0) (a : ℝ) (k : ℕ) :
    (∫ z : ℂ, ‖z‖^k ∂ComplexRootPoissonLaw.law r a) =
      ∫ n, (∫ ω, ‖terminal n a ω‖^k ∂probability n) ∂poissonMeasure r := by
  have he := integral_growth r a (fun z : ℂ => ((‖z‖^k : ℝ) : ℂ))
    (by fun_prop) ((1+2*|a|)^k) (fun n ω => by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (norm_nonneg _) k)] using terminal_power_bound n k a ω)
  simp only [integral_complex_ofReal] at he
  exact Complex.ofReal_injective he

theorem normalized_growth_bound (a : ℝ) (F : ℂ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hB : ∀ n (ω : Sample n), ‖F (terminal n a ω)‖ ≤ A*B^n)
    (n : ℕ) (ω : Sample n) : ‖(A : ℂ)⁻¹*F (terminal n a ω)‖ ≤ B^n := by
  calc
    _ = A⁻¹*‖F (terminal n a ω)‖ := by
      simp [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
    _ ≤ A⁻¹*(A*B^n) := mul_le_mul_of_nonneg_left (hB n ω) (inv_nonneg.mpr hA.le)
    _ = _ := by field_simp [hA.ne']

theorem growth_integrable_with_constant (r : ℝ≥0) (a : ℝ) (F : ℂ → ℂ) (hF : Continuous F)
    (A B : ℝ) (hA : 0 < A)
    (hB : ∀ n (ω : Sample n), ‖F (terminal n a ω)‖ ≤ A*B^n) :
    Integrable F (ComplexRootPoissonLaw.law r a) := by
  have hi := growth_integrable r a (fun z => (A : ℂ)⁻¹*F z) (by fun_prop) B
    (normalized_growth_bound a F A B hA hB)
  have hAC : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  convert hi.const_mul (A : ℂ) using 1
  funext z
  simp [hAC]

theorem growth_mixture_with_constant (r : ℝ≥0) (a : ℝ) (F : ℂ → ℂ) (hF : Continuous F)
    (A B : ℝ) (hA : 0 < A)
    (hB : ∀ n (ω : Sample n), ‖F (terminal n a ω)‖ ≤ A*B^n) :
    (∫ z, F z ∂ComplexRootPoissonLaw.law r a) =
      ∫ n, (∫ ω, F (terminal n a ω) ∂probability n) ∂poissonMeasure r := by
  have he := integral_growth r a (fun z => (A : ℂ)⁻¹*F z) (by fun_prop) B
    (normalized_growth_bound a F A B hA hB)
  simp_rw [integral_const_mul] at he
  exact mul_left_cancel₀ (inv_ne_zero (Complex.ofReal_ne_zero.mpr hA.ne')) he

theorem shifted_power_bound (n k : ℕ) (a : ℝ) (z : ℂ) (ω : Sample n) :
    ‖(z+terminal n a ω)^k‖ ≤ (1+‖z‖)^k*((1+2*|a|)^k)^n := by
  have h1 : 1 ≤ (1+2*|a|)^n := one_le_pow₀ (by have ha := abs_nonneg a; linarith)
  have hb : ‖z+terminal n a ω‖ ≤ (1+‖z‖)*(1+2*|a|)^n := by
    have he := norm_add_le z (terminal n a ω)
    have hs := terminal_geometric_bound n a ω
    have hz := norm_nonneg z
    nlinarith
  have he := pow_le_pow_left₀ (norm_nonneg _) hb k
  simpa only [norm_pow, mul_pow, ← pow_mul, Nat.mul_comm n k] using he

theorem shifted_power_integrable (r : ℝ≥0) (a : ℝ) (z : ℂ) (k : ℕ) :
    Integrable (fun y : ℂ => (z+y)^k) (ComplexRootPoissonLaw.law r a) :=
  growth_integrable_with_constant r a _ (by fun_prop) ((1+‖z‖)^k) ((1+2*|a|)^k)
    (by positivity) (fun n ω => shifted_power_bound n k a z ω)

theorem shifted_power_mixture (r : ℝ≥0) (a : ℝ) (z : ℂ) (k : ℕ) :
    (∫ y : ℂ, (z+y)^k ∂ComplexRootPoissonLaw.law r a) =
      ∫ n, (∫ ω, (z+terminal n a ω)^k ∂probability n) ∂poissonMeasure r :=
  growth_mixture_with_constant r a _ (by fun_prop) ((1+‖z‖)^k) ((1+2*|a|)^k)
    (by positivity) (fun n ω => shifted_power_bound n k a z ω)

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonPolynomialDomain
