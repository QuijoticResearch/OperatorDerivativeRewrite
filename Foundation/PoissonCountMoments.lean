import Foundation.PoissonEntireMoments
import Foundation.PoissonMoments
import Mathlib.Algebra.Order.Ring.Pow

/-! Native integrability and exact first and second moments of the actual Poisson count. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.PoissonCountMoments
open ComplexRootPoissonLaw

theorem count_power_integrable (r : ℝ≥0) (k : ℕ) :
    Integrable (fun n : ℕ => (n : ℝ)^k) (poissonMeasure r) := by
  apply (PoissonEntireMoments.real_powers_integrable r ((2 : ℝ)^k)).mono'
    StronglyMeasurable.of_discrete.aestronglyMeasurable
  apply Eventually.of_forall
  intro n
  have hb : (n : ℝ) ≤ (2 : ℝ)^n := by
    have he := one_add_mul_le_pow (a := (1 : ℝ)) (by norm_num) n
    norm_num at he
    linarith
  have he := pow_le_pow_left₀ (Nat.cast_nonneg n) hb k
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) k)]
  simpa only [← pow_mul, Nat.mul_comm n k] using he

theorem count_integrable (r : ℝ≥0) : Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  simpa only [pow_one] using count_power_integrable r 1

theorem weighted_count (r : ℝ≥0) : HasSum (fun n : ℕ => weight r n*(n : ℝ)) (r : ℝ) := by
  apply (hasSum_nat_add_iff' 1).mp
  have he (n : ℕ) : weight r (n+1)*((n+1 : ℕ) : ℝ) = (r : ℝ)*weight r n := by
    simp only [weight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    field_simp [hn] <;> ring
  simpa only [Finset.sum_range_one, Nat.cast_zero, mul_zero, sub_zero, he, mul_one] using
    (weight_hasSum r).mul_left (r : ℝ)

theorem count_integral (r : ℝ≥0) : (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = (r : ℝ) := by
  by_cases hr : r = 0
  · subst r
    apply (hasSum_integral_poissonMeasure (count_integrable 0)).unique
    simpa only [weight, smul_eq_mul] using weighted_count 0
  · exact PoissonMoments.integral_poisson_count r (pos_iff_ne_zero.mpr hr)

theorem weighted_factorial_second (r : ℝ≥0) :
    HasSum (fun n : ℕ => weight r n*((n : ℝ)*((n : ℝ)-1))) ((r : ℝ)^2) := by
  apply (hasSum_nat_add_iff' 2).mp
  have he (n : ℕ) : weight r (n+2)*(((n+2 : ℕ) : ℝ)*(((n+2 : ℕ) : ℝ)-1)) =
      (r : ℝ)^2*weight r n := by
    simp only [weight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
    have hn2 : (n : ℝ)+1+1 ≠ 0 := by positivity
    field_simp [hn1, hn2] <;> ring
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, zero_mul, sub_self, mul_zero, zero_add, sub_zero, he, mul_one] using
    (weight_hasSum r).mul_left ((r : ℝ)^2)

theorem factorial_second_integral (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ)*((n : ℝ)-1) ∂poissonMeasure r) = (r : ℝ)^2 := by
  have hi : Integrable (fun n : ℕ => (n : ℝ)*((n : ℝ)-1)) (poissonMeasure r) := by
    convert (count_power_integrable r 2).sub (count_integrable r) using 1
    funext n
    simp only [Pi.sub_apply]
    ring
  apply (hasSum_integral_poissonMeasure hi).unique
  simpa only [weight, smul_eq_mul] using weighted_factorial_second r

theorem square_integral (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ)^2 ∂poissonMeasure r) = (r : ℝ)^2+(r : ℝ) := by
  by_cases hr : r = 0
  · subst r
    have he (n : ℕ) : (n : ℝ)^2 = (n : ℝ)*((n : ℝ)-1)+(n : ℝ) := by ring
    simp_rw [he]
    rw [integral_add]
    · rw [factorial_second_integral, count_integral]
    · convert (count_power_integrable 0 2).sub (count_integrable 0) using 1
      funext n
      simp only [Pi.sub_apply]
      ring
    · exact count_integrable 0
  · exact PoissonMoments.integral_poisson_count_sq r (pos_iff_ne_zero.mpr hr)

end OperatorDerivativeRewrite.Foundation.PoissonCountMoments
