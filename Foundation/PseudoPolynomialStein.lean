import Foundation.PseudoMomentPositivity
import Mathlib.Algebra.Polynomial.Derivative

/-! An actual algebraic pure-order moment functional and polynomial Stein identity.
No positive norm, measure, or nonpolynomial completion is introduced. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PseudoPolynomialStein
open Polynomial

def moment (p : ℕ) (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => (p : ℝ)*a*(n.descFactorial (p-1) : ℝ)*moment p a (n-(p-1))
termination_by n => n

theorem moment_zero (p : ℕ) (a : ℝ) : moment p a 0 = 1 := by rw [moment]

theorem moment_succ (p n : ℕ) (a : ℝ) :
    moment p a (n+1) = (p : ℝ)*a*(n.descFactorial (p-1) : ℝ)*moment p a (n-(p-1)) := by
  rw [moment]

def expectation (p : ℕ) (a : ℝ) : Polynomial ℝ →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun n => moment p a n • LinearMap.id

theorem expectation_monomial (p n : ℕ) (a c : ℝ) :
    expectation p a (monomial n c) = c * moment p a n := by
  simp [expectation, Polynomial.lsum, smul_eq_mul, mul_comm]

theorem expectation_X_pow (p n : ℕ) (a : ℝ) : expectation p a (X^n) = moment p a n := by
  simpa only [monomial_one_right_eq_X_pow, one_mul] using expectation_monomial p n a 1

theorem stein_X_pow (p n : ℕ) (a : ℝ) :
    expectation p a (X * X^n) = (p : ℝ)*a * expectation p a (derivative^[p-1] (X^n)) := by
  rw [← pow_succ', iterate_derivative_X_pow_eq_smul, map_smul,
    expectation_X_pow, expectation_X_pow, moment_succ]
  simp only [smul_eq_mul]
  ring

theorem polynomial_stein (p : ℕ) (a : ℝ) (g : Polynomial ℝ) :
    expectation p a (X*g) = (p : ℝ)*a * expectation p a (derivative^[p-1] g) := by
  induction g using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [mul_add, map_add, ← Module.End.pow_apply, map_add,
      Module.End.pow_apply, Module.End.pow_apply, map_add, hP, hQ, mul_add]
  | monomial n c =>
    have he : monomial n c = c • (X : Polynomial ℝ)^n := by
      rw [smul_eq_C_mul, C_mul_X_pow_eq_monomial]
    rw [he, mul_smul_comm, iterate_derivative_smul, map_smul, map_smul, stein_X_pow]
    simp only [smul_eq_mul]
    ring

theorem moment_off_order (p : ℕ) (hp : 0 < p) (a : ℝ) (n : ℕ)
    (hn : ¬ p ∣ n) : moment p a n = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact (hn (dvd_zero p)).elim
    | succ n =>
      rw [moment_succ]
      by_cases hsmall : n < p-1
      · rw [Nat.descFactorial_of_lt hsmall]
        simp
      · have hlarge : p-1 ≤ n := by omega
        have hsum : n+1 = (n-(p-1))+p := by omega
        have hnot : ¬ p ∣ n-(p-1) := by
          intro hd
          apply hn
          rw [hsum]
          exact dvd_add hd (dvd_refl p)
        rw [ih _ (by omega) hnot, mul_zero]

theorem moment_leading (p : ℕ) (hp : 0 < p) (a : ℝ) :
    moment p a p = (p.factorial : ℝ)*a := by
  have he : p-1+1 = p := by omega
  calc
    moment p a p = moment p a (p-1+1) := congrArg (moment p a) he.symm
    _ = (p : ℝ)*a*((p-1).factorial : ℝ) := by
      rw [moment_succ, Nat.sub_self, moment_zero, Nat.descFactorial_self, mul_one]
    _ = (p.factorial : ℝ)*a := by
      rw [← Nat.mul_factorial_pred (ne_of_gt hp), Nat.cast_mul]
      ring

theorem stein_moments_unique (p : ℕ) (a : ℝ) (E : Polynomial ℝ →ₗ[ℝ] ℝ)
    (h1 : E 1 = 1)
    (hstein : ∀ g : Polynomial ℝ, E (X*g) = (p : ℝ)*a*E (derivative^[p-1] g))
    (n : ℕ) : E (X^n) = moment p a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [pow_zero, moment_zero] using h1
    | succ n =>
      rw [pow_succ', hstein, iterate_derivative_X_pow_eq_smul, map_smul,
        ih _ (by omega), moment_succ]
      simp only [smul_eq_mul]
      ring

/-- Normalization and the polynomial Stein identity characterize the whole functional. -/
theorem expectation_unique (p : ℕ) (a : ℝ) (E : Polynomial ℝ →ₗ[ℝ] ℝ)
    (h1 : E 1 = 1)
    (hstein : ∀ g : Polynomial ℝ, E (X*g) = (p : ℝ)*a*E (derivative^[p-1] g)) :
    E = expectation p a := by
  apply LinearMap.ext
  intro g
  induction g using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ]
  | monomial n c =>
    have he : monomial n c = c • (X : Polynomial ℝ)^n := by
      rw [smul_eq_C_mul, C_mul_X_pow_eq_monomial]
    rw [he, map_smul, map_smul, expectation_X_pow, stein_moments_unique p a E h1 hstein]

theorem expectation_not_positive (p : ℕ) (hp : 2 < p) (a : ℝ) (ha : a ≠ 0) :
    ¬ ∀ R : Polynomial ℝ, 0 ≤ expectation p a (R^2) := by
  apply PseudoMomentPositivity.pure_order_not_square_positive (expectation p a) p hp
  · intro n hn
    rw [expectation_X_pow]
    exact moment_off_order p (by omega) a n hn
  · rw [expectation_X_pow, moment_leading p (by omega)]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero p) ha

theorem moment_multiple_factorial (p : ℕ) (hp : 0 < p) (a : ℝ) (k : ℕ) :
    moment p a (p*k) * (k.factorial : ℝ) = ((p*k).factorial : ℝ)*a^k := by
  induction k with
  | zero => simp [moment_zero]
  | succ k ih =>
    have hn : p*(k+1) = (p*k+p-1)+1 := by rw [Nat.mul_add, Nat.mul_one]; omega
    have hsub : (p*k+p-1)-(p-1) = p*k := by omega
    have hd : (p-1) ≤ p*k+p-1 := by omega
    have hf : ((p*k).factorial : ℝ) *
        ((p*k+p-1).descFactorial (p-1) : ℝ) = ((p*k+p-1).factorial : ℝ) := by
      have h := Nat.factorial_mul_descFactorial hd
      rw [hsub] at h
      exact_mod_cast h
    have hb : ((p*(k+1)).factorial : ℝ) =
        (p : ℝ)*(k+1 : ℕ)*((p*k+p-1).factorial : ℝ) := by
      have h := Nat.mul_factorial_pred (show p*(k+1) ≠ 0 by positivity)
      rw [Nat.mul_add, Nat.mul_one] at h
      exact_mod_cast h.symm
    have hs : moment p a (p*(k+1)) = (p : ℝ)*a*
        ((p*k+p-1).descFactorial (p-1) : ℝ)*moment p a (p*k) := by
      calc
        moment p a (p*(k+1)) = moment p a ((p*k+p-1)+1) := congrArg (moment p a) hn
        _ = _ := by rw [moment_succ, hsub]
    rw [hs, Nat.factorial_succ, Nat.cast_mul]
    calc
      _ = (p : ℝ)*(k+1 : ℕ)*a*(moment p a (p*k)*(k.factorial : ℝ))*
          ((p*k+p-1).descFactorial (p-1) : ℝ) := by ring
      _ = (p : ℝ)*(k+1 : ℕ)*a*(((p*k).factorial : ℝ)*
          ((p*k+p-1).descFactorial (p-1) : ℝ))*a^k := by rw [ih]; ring
      _ = _ := by rw [hf, hb, pow_succ]; ring

theorem moment_multiple (p : ℕ) (hp : 0 < p) (a : ℝ) (k : ℕ) :
    moment p a (p*k) = ((p*k).factorial : ℝ)*a^k/(k.factorial : ℝ) := by
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero k)).2
  exact moment_multiple_factorial p hp a k

end OperatorDerivativeRewrite.Foundation.PseudoPolynomialStein
