import Foundation.MixedCubicThirdDegree
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! A genuine probability law realizes the first four mixed moments, but not the full sequence. -/
noncomputable section
open MeasureTheory Polynomial
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.MixedCubicAtomicRealization
open MixedCubicMomentPositivity
set_option backward.isDefEq.respectTransparency false

def law : Measure ℝ :=
  (1/3 : ℝ≥0∞) • Measure.dirac (-1) + (1/2 : ℝ≥0∞) • Measure.dirac 0 +
    (1/6 : ℝ≥0∞) • Measure.dirac 2

instance law_probability : IsProbabilityMeasure law := by
  constructor
  norm_num [law, Measure.add_apply, Measure.smul_apply]
  apply (ENNReal.toReal_eq_one_iff _).mp
  norm_num [ENNReal.toReal_add]

theorem atom_integrable (f : ℝ → ℝ) (x : ℝ) (c : ℝ≥0∞) (hc : c ≠ ∞) :
    Integrable f (c • Measure.dirac x) :=
  (integrable_dirac (by simp)).smul_measure hc

theorem law_integrable (f : ℝ → ℝ) : Integrable f law := by
  exact ((atom_integrable f (-1) (1/3) (by norm_num)).add_measure
    (atom_integrable f 0 (1/2) (by norm_num))).add_measure
      (atom_integrable f 2 (1/6) (by norm_num))

theorem law_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂law) = (1/3 : ℝ)*f (-1)+(1/2 : ℝ)*f 0+(1/6 : ℝ)*f 2 := by
  have h0 := atom_integrable f (-1) (1/3) (by norm_num)
  have h1 := atom_integrable f 0 (1/2) (by norm_num)
  have h2 := atom_integrable f 2 (1/6) (by norm_num)
  rw [law, integral_add_measure (h0.add_measure h1) h2, integral_add_measure h0 h1]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  norm_num

def atomicExpectation : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun g := ∫ x, g.eval x ∂law
  map_add' P Q := by
    simpa only [eval_add] using integral_add
      (law_integrable (fun x => P.eval x)) (law_integrable (fun x => Q.eval x))
  map_smul' c P := by
    simp only [eval_smul, smul_eq_mul, integral_const_mul, RingHom.id_apply]

theorem atomicExpectation_apply (g : Polynomial ℝ) :
    atomicExpectation g = ∫ x, g.eval x ∂law := rfl

theorem atomic_X_pow (n : ℕ) :
    atomicExpectation (X^n) = (1/3 : ℝ)*(-1)^n+(1/2 : ℝ)*0^n+(1/6 : ℝ)*2^n := by
  rw [atomicExpectation_apply, law_integral]
  simp only [eval_pow, eval_X]

theorem power_match_through_four (n : ℕ) (hn : n ≤ 4) :
    atomicExpectation (X^n) = expectation 1 1 (X^n) := by
  rw [atomic_X_pow, expectation_X_pow]
  interval_cases n <;> norm_num [moment]

theorem polynomial_match_through_four (g : Polynomial ℝ) (hg : g.natDegree ≤ 4) :
    atomicExpectation g = expectation 1 1 g := by
  conv_lhs => rw [g.as_sum_range' 5 (by omega)]
  conv_rhs => rw [g.as_sum_range' 5 (by omega)]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have he : monomial n (g.coeff n) = g.coeff n • (X : Polynomial ℝ)^n := by
    rw [smul_eq_C_mul, C_mul_X_pow_eq_monomial]
  rw [he, map_smul, map_smul, power_match_through_four n (by
    have := Finset.mem_range.mp hn
    omega)]

theorem quadratic_square_match (g : Polynomial ℝ) (hg : g.natDegree ≤ 2) :
    (∫ x, (g.eval x)^2 ∂law) = expectation 1 1 (g^2) := by
  have hd : (g^2).natDegree ≤ 4 := by rw [natDegree_pow]; omega
  simpa only [atomicExpectation_apply, eval_pow] using polynomial_match_through_four (g^2) hd

theorem later_moments :
    (∫ x : ℝ, x^5 ∂law) = 5 ∧ expectation 1 1 (X^5) = 10 ∧
      (∫ x : ℝ, x^6 ∂law) = 11 ∧ expectation 1 1 (X^6) = 25 := by
  norm_num [law_integral, expectation_X_pow, moment]

theorem witness_square_integral : (∫ x, (cubicWitness.eval x)^2 ∂law) = 25 := by
  rw [law_integral]
  simp only [cubicWitness, eval_add, eval_sub, eval_pow, eval_smul, eval_X, smul_eq_mul]
  norm_num

theorem same_quadratic_tests_opposite_cubic :
    (∀ g : Polynomial ℝ, g.natDegree ≤ 2 →
      (∫ x, (g.eval x)^2 ∂law) = expectation 1 1 (g^2)) ∧
      (∫ x, (cubicWitness.eval x)^2 ∂law) = 25 ∧
        expectation 1 1 (cubicWitness^2) = -21 :=
  ⟨quadratic_square_match, witness_square_integral, cubic_witness_value⟩

theorem no_measure_full_polynomial_match (μ : Measure ℝ) :
    ¬ ∀ g : Polynomial ℝ, (∫ x, g.eval x ∂μ) = expectation 1 1 g := by
  intro hm
  have hp : 0 ≤ ∫ x, (cubicWitness^2).eval x ∂μ := by
    apply integral_nonneg
    intro x
    simpa only [eval_pow, Pi.zero_apply] using sq_nonneg (cubicWitness.eval x)
  rw [hm, cubic_witness_value] at hp
  norm_num at hp

end OperatorDerivativeRewrite.Foundation.MixedCubicAtomicRealization
