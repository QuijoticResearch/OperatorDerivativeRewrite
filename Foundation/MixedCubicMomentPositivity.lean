import Foundation.PseudoPolynomialStein
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! An actual mixed Gaussian/cubic moment functional and its exact quadratic-square test. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.MixedCubicMomentPositivity
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def moment (v k : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => v*(n : ℝ)*moment v k (n-1) +
      (k/2)*(n.descFactorial 2 : ℝ)*moment v k (n-2)
termination_by n => n

def expectation (v k : ℝ) : Polynomial ℝ →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun n => moment v k n • LinearMap.id

theorem expectation_monomial (v k c : ℝ) (n : ℕ) :
    expectation v k (monomial n c) = c*moment v k n := by
  simp [expectation, Polynomial.lsum, smul_eq_mul, mul_comm]

theorem expectation_X_pow (v k : ℝ) (n : ℕ) :
    expectation v k (X^n) = moment v k n := by
  simpa only [monomial_one_right_eq_X_pow, one_mul] using expectation_monomial v k 1 n

theorem low_moments (v k : ℝ) :
    moment v k 0 = 1 ∧ moment v k 1 = 0 ∧ moment v k 2 = v ∧
      moment v k 3 = k ∧ moment v k 4 = 3*v^2 := by
  norm_num [moment]
  ring

def quadratic (c b a : ℝ) : Polynomial ℝ := c • 1 + b • X + a • X^2

theorem quadratic_natDegree (c b a : ℝ) : (quadratic c b a).natDegree ≤ 2 := by
  have he : quadratic c b a = C a*X^2+C b*X+C c := by
    simp only [quadratic, smul_eq_C_mul, mul_one]
    ring
  rw [he]
  exact natDegree_le_of_degree_le degree_quadratic_le

theorem quadratic_of_natDegree (g : Polynomial ℝ) (hg : g.natDegree ≤ 2) :
    g = quadratic (g.coeff 0) (g.coeff 1) (g.coeff 2) := by
  ext n
  rcases n with _ | (_ | (_ | n))
  · norm_num only [quadratic, coeff_add, coeff_smul, coeff_one, coeff_X, coeff_X_pow,
      smul_eq_mul]
    simp only [ite_true, ite_false, mul_one, mul_zero, add_zero]
  · norm_num only [quadratic, coeff_add, coeff_smul, coeff_one, coeff_X, coeff_X_pow,
      smul_eq_mul]
    simp only [ite_true, ite_false, mul_one, mul_zero, zero_add, add_zero]
  · norm_num only [quadratic, coeff_add, coeff_smul, coeff_one, coeff_X, coeff_X_pow,
      smul_eq_mul]
    simp only [ite_true, ite_false, mul_one, mul_zero, zero_add, add_zero]
  · have hz := natDegree_le_iff_coeff_eq_zero.mp hg (n+3) (by omega)
    change g.coeff (n+3) = _
    rw [hz]
    simp only [quadratic, coeff_add, coeff_smul, coeff_one, coeff_X, coeff_X_pow,
      ite_eq_right (show n+3 ≠ 0 by omega), ite_eq_right (show 1 ≠ n+3 by omega),
      ite_eq_right (show n+3 ≠ 2 by omega), smul_zero, zero_add]

theorem quadratic_square (v k c b a : ℝ) :
    expectation v k ((quadratic c b a)^2) =
      c^2+v*b^2+2*v*c*a+2*k*b*a+3*v^2*a^2 := by
  have he : (quadratic c b a)^2 = c^2 • (X : Polynomial ℝ)^0 +
      (2*c*b) • X^1 + (b^2+2*c*a) • X^2 + (2*b*a) • X^3 + a^2 • X^4 := by
    simp only [quadratic, Algebra.smul_def, map_add, map_mul, map_pow,
      map_ofNat, pow_zero, pow_one]
    ring
  rw [he]
  simp only [map_add, map_smul, expectation_X_pow, smul_eq_mul]
  rcases low_moments v k with ⟨h0,h1,h2,h3,h4⟩
  rw [h0,h1,h2,h3,h4]
  ring

/-- A division-free Schur/completed-square identity for the finite moment matrix. -/
theorem weighted_square_decomposition (v k c b a : ℝ) :
    v*expectation v k ((quadratic c b a)^2) =
      v*(c+v*a)^2+(v*b+k*a)^2+(2*v^3-k^2)*a^2 := by
  rw [quadratic_square]
  ring

theorem negative_square_witness_value (v k : ℝ) :
    expectation v k ((quadratic (-v^2) (-k) v)^2) = v*(2*v^3-k^2) := by
  rw [quadratic_square]
  ring

theorem quadratic_square_nonneg (v k : ℝ) (hv : 0 < v) (hk : k^2 ≤ 2*v^3)
    (c b a : ℝ) : 0 ≤ expectation v k ((quadratic c b a)^2) := by
  have hn := add_nonneg (add_nonneg (mul_nonneg hv.le (sq_nonneg (c+v*a)))
    (sq_nonneg (v*b+k*a))) (mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg a))
  rw [← weighted_square_decomposition] at hn
  exact (mul_nonneg_iff_of_pos_left hv).mp hn

theorem quadratic_positivity_iff (v k : ℝ) :
    (∀ g : Polynomial ℝ, g.natDegree ≤ 2 → 0 ≤ expectation v k (g^2)) ↔
      0 ≤ v ∧ k^2 ≤ 2*v^3 := by
  constructor
  · intro hpos
    have hX := hpos (quadratic 0 1 0) (quadratic_natDegree 0 1 0)
    rw [quadratic_square] at hX
    have hv : 0 ≤ v := by nlinarith
    refine ⟨hv, ?_⟩
    by_cases hz : v = 0
    · have hq := hpos (quadratic 0 1 (-k)) (quadratic_natDegree 0 1 (-k))
      rw [quadratic_square, hz] at hq
      rw [hz]
      nlinarith [sq_nonneg k]
    · have hp : 0 < v := lt_of_le_of_ne hv (Ne.symm hz)
      have hw := hpos (quadratic (-v^2) (-k) v) (quadratic_natDegree _ _ _)
      rw [negative_square_witness_value] at hw
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hp).mp hw)
  · rintro ⟨hv,hk⟩ g hg
    rw [quadratic_of_natDegree g hg]
    by_cases hz : v = 0
    · have hk0 : k = 0 := by rw [hz] at hk; nlinarith [sq_nonneg k]
      rw [quadratic_square, hz, hk0]
      nlinarith [sq_nonneg (g.coeff 0)]
    · exact quadratic_square_nonneg v k (lt_of_le_of_ne hv (Ne.symm hz)) hk _ _ _

theorem stein_X_pow (v k : ℝ) (n : ℕ) :
    expectation v k (X*X^n) = v*expectation v k (derivative (X^n)) +
      (k/2)*expectation v k (derivative^[2] (X^n)) := by
  rw [← pow_succ', derivative_X_pow, ← smul_eq_C_mul,
    iterate_derivative_X_pow_eq_smul, map_smul, map_smul,
    expectation_X_pow, expectation_X_pow, expectation_X_pow, moment]
  simp only [smul_eq_mul]
  ring

theorem polynomial_stein (v k : ℝ) (g : Polynomial ℝ) :
    expectation v k (X*g) = v*expectation v k g.derivative +
      (k/2)*expectation v k (derivative^[2] g) := by
  induction g using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have hi : derivative^[2] (P+Q) = derivative^[2] P + derivative^[2] Q := by
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, derivative_add]
    rw [mul_add, map_add, derivative_add, map_add, hi, map_add, hP, hQ]
    ring
  | monomial n c =>
    have he : monomial n c = c • (X : Polynomial ℝ)^n := by
      rw [smul_eq_C_mul, C_mul_X_pow_eq_monomial]
    rw [he, mul_smul_comm, derivative_smul, iterate_derivative_smul,
      map_smul, map_smul, map_smul, stein_X_pow]
    simp only [smul_eq_mul]
    ring

def cubicWitness : Polynomial ℝ := X^3 - (6 : ℝ) • X^2 + (3 : ℝ) • X^1 + (5 : ℝ) • X^0

theorem cubic_witness_value : expectation 1 1 (cubicWitness^2) = -21 := by
  have he : cubicWitness^2 = (X : Polynomial ℝ)^6 - (12 : ℝ) • X^5 + (42 : ℝ) • X^4 -
      (26 : ℝ) • X^3 - (51 : ℝ) • X^2 + (30 : ℝ) • X^1 + (25 : ℝ) • X^0 := by
    simp only [cubicWitness, Algebra.smul_def, map_ofNat, pow_zero, pow_one]
    ring
  rw [he]
  simp only [map_add, map_sub, map_smul, expectation_X_pow, smul_eq_mul]
  norm_num [moment]

theorem quadratic_tests_pass_but_cubic_fails :
    (∀ g : Polynomial ℝ, g.natDegree ≤ 2 → 0 ≤ expectation 1 1 (g^2)) ∧
      expectation 1 1 (cubicWitness^2) < 0 := by
  refine ⟨(quadratic_positivity_iff 1 1).mpr (by norm_num), ?_⟩
  rw [cubic_witness_value]
  norm_num

theorem gaussian_axis (v : ℝ) :
    expectation v 0 = PseudoPolynomialStein.expectation 2 (v/2) := by
  apply PseudoPolynomialStein.expectation_unique 2 (v/2)
  · change expectation v 0 (X^0) = 1
    rw [expectation_X_pow]
    exact (low_moments v 0).1
  · intro g
    simpa only [zero_div, zero_mul, add_zero, Nat.reduceSub, Function.iterate_one,
      Nat.cast_ofNat, show (2 : ℝ)*(v/2) = v by ring] using polynomial_stein v 0 g

theorem pure_cubic_axis (k : ℝ) :
    expectation 0 k = PseudoPolynomialStein.expectation 3 (k/6) := by
  apply PseudoPolynomialStein.expectation_unique 3 (k/6)
  · change expectation 0 k (X^0) = 1
    rw [expectation_X_pow]
    exact (low_moments 0 k).1
  · intro g
    simpa only [zero_mul, zero_add, Nat.reduceSub, Nat.cast_ofNat,
      show (3 : ℝ)*(k/6) = k/2 by ring] using polynomial_stein 0 k g

end OperatorDerivativeRewrite.Foundation.MixedCubicMomentPositivity
