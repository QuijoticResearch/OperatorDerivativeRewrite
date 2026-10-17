import Foundation.ComplexRootPoissonLaw
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Actual Poisson exponential moments, including noncontractive complex powers. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonEntireMoments
open ComplexRootPoissonLaw

theorem weighted_real_powers (r : ℝ≥0) (c : ℝ) :
    HasSum (fun n => weight r n * c^n) (Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ)*c)) := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*c)).mul_left
    (Real.exp (-(r : ℝ)))
  convert hs using 1
  · funext n
    simp only [weight, mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ]

theorem real_powers_integrable (r : ℝ≥0) (c : ℝ) :
    Integrable (fun n : ℕ => c^n) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [weight, norm_pow, Real.norm_eq_abs] using
    (weighted_real_powers r |c|).summable

theorem complex_powers_integrable (r : ℝ≥0) (z : ℂ) :
    Integrable (fun n : ℕ => z^n) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [weight, norm_pow] using (weighted_real_powers r ‖z‖).summable

theorem complex_powers_integral (r : ℝ≥0) (z : ℂ) :
    (∫ n : ℕ, z^n ∂poissonMeasure r) = Complex.exp ((r : ℂ)*(z-1)) := by
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ((r : ℝ) • z)).const_smul
    (Real.exp (-(r : ℝ)))
  have he : (fun n : ℕ => weight r n • z^n) =
      (fun n => Real.exp (-(r : ℝ)) • ((n.factorial : ℝ)⁻¹ • ((r : ℝ) • z)^n)) := by
    funext n
    rw [smul_pow, smul_smul, smul_smul]
    congr 1
    simp only [weight, div_eq_mul_inv]
    ring
  have hi : (∫ n : ℕ, z^n ∂poissonMeasure r) =
      Real.exp (-(r : ℝ)) • NormedSpace.exp ((r : ℝ) • z) :=
    (hasSum_integral_poissonMeasure (complex_powers_integrable r z)).unique (he ▸ hs)
  rw [hi, Complex.real_smul, Complex.real_smul, ← Complex.exp_eq_exp_ℂ,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem real_powers_integral (r : ℝ≥0) (c : ℝ) :
    (∫ n : ℕ, c^n ∂poissonMeasure r) = Real.exp ((r : ℝ)*(c-1)) := by
  have he := hasSum_integral_poissonMeasure (real_powers_integrable r c)
  have hs := (weighted_real_powers r c)
  have ht : (∫ n : ℕ, c^n ∂poissonMeasure r) =
      Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ)*c) := by
    exact he.unique (by simpa only [weight, smul_eq_mul] using hs)
  rw [ht, ← Real.exp_add]
  congr 1
  ring

theorem exponential_integrable (r : ℝ≥0) (c : ℝ) :
    Integrable (fun n : ℕ => Real.exp ((n : ℝ)*c)) (poissonMeasure r) := by
  simpa only [Real.exp_nat_mul] using real_powers_integrable r (Real.exp c)

theorem exponential_integral (r : ℝ≥0) (c : ℝ) :
    (∫ n : ℕ, Real.exp ((n : ℝ)*c) ∂poissonMeasure r) =
      Real.exp ((r : ℝ)*(Real.exp c-1)) := by
  simpa only [Real.exp_nat_mul] using real_powers_integral r (Real.exp c)

end OperatorDerivativeRewrite.Foundation.PoissonEntireMoments
