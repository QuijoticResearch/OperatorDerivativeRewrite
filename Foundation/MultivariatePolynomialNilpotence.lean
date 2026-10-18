import Foundation.MultivariateFactorialDomain
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Degree decrease and local nilpotence of actual polynomial directional derivatives. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.MultivariatePolynomialNilpotence
open MultivariateFactorialDomain
variable {ι : Type*}

theorem derivative_degree_drop (v : ι → ℝ) (n : ℕ) (P : MvPolynomial ι ℝ)
    (hP : P.totalDegree ≤ n + 1) : (polynomialDerivative v P).totalDegree ≤ n := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [polynomialDerivative_monomial]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  have hd' : d.degree ≤ n+1 := by
    exact (MvPolynomial.le_totalDegree hd).trans hP
  have hl := lower_degree d i hi
  have hm := MvPolynomial.totalDegree_monomial_le (d-Finsupp.single i 1) (P.coeff d*(d i:ℝ)*v i)
  have hb : (d-Finsupp.single i 1).degree ≤ n := by omega
  exact hm.trans hb

theorem iterate_zero_of_degree_le (v : ι → ℝ) (n : ℕ) (P : MvPolynomial ι ℝ)
    (hP : P.totalDegree ≤ n) :
    (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[n+1] P = 0 := by
  induction n generalizing P with
  | zero =>
    have he := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hP)
    rw [he, Function.iterate_one]
    exact MvPolynomial.derivation_C _ _
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (polynomialDerivative v P) (derivative_degree_drop v n P hP)

theorem iterate_zero (v : ι → ℝ) (P : MvPolynomial ι ℝ) (k : ℕ)
    (hk : P.totalDegree < k) :
    (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[k] P = 0 := by
  cases k with
  | zero => omega
  | succ k => exact iterate_zero_of_degree_le v k P (by omega)

theorem completed_iterate_zero [DecidableEq ι] (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1)
    (P : MvPolynomial ι ℝ) (k : ℕ) (hk : P.totalDegree < k) :
    ((derivative v hv)^k) (polynomial P) = 0 := by
  rw [derivative_iterate_core, iterate_zero v P k hk]
  exact polynomialMap.map_zero

end OperatorDerivativeRewrite.Foundation.MultivariatePolynomialNilpotence
