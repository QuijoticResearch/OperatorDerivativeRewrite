import Foundation.QuarticAppellExpansion

/-! The highest nonzero Appell pairing with monomials, without a global dual assumption. -/
noncomputable section
open Polynomial
namespace OperatorDerivativeRewrite.Foundation.QuarticAppellPairing
open QuarticAppellCalculus PseudoPolynomialStein PseudoClarkOconeObstruction

theorem appell_iterate (a : ℝ) (k n : ℕ) :
    derivative^[k] (appell a n) = (n.descFactorial k : ℝ) • appell a (n-k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp [appell, iterate_derivative_one (Nat.zero_lt_succ k)]
    | succ n =>
      rw [Function.iterate_succ_apply, appell_derivative, iterate_derivative_smul,
        ih, Nat.succ_descFactorial_succ, Nat.cast_mul, smul_smul, Nat.succ_sub_succ]
      norm_cast

theorem pair_recurrence (a : ℝ) (n d : ℕ) :
    pairing 4 a (appell a n) (X^(d+1)) =
      pairing 4 a (appell a (n+1)) (X^d) +
      (4*a*(n.descFactorial 3 : ℝ)) * pairing 4 a (appell a (n-3)) (X^d) := by
  have hx : appell a n * X^(d+1) = appell a (n+1) * X^d +
      (4*a*(n.descFactorial 3 : ℝ)) • (appell a (n-3) * X^d) := by
    rw [appell, raise, appell_iterate, smul_smul]
    simp only [smul_eq_C_mul, map_mul]
    ring
  simp only [pairing]
  rw [hx, map_add, map_smul]
  rfl

theorem above_degree_zero (a : ℝ) (d n : ℕ) (hn : 3*d < n) :
    pairing 4 a (appell a n) (X^d) = 0 := by
  induction d generalizing n with
  | zero =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa only [pairing, pow_zero, mul_one] using appell_mean_zero a k
  | succ d ih =>
    rw [pair_recurrence, ih (n+1) (by omega), ih (n-3) (by omega)]
    ring

theorem top_pairing (a : ℝ) (d : ℕ) :
    pairing 4 a (appell a (3*d)) (X^d) = ((3*d).factorial : ℝ)*(4*a)^d := by
  induction d with
  | zero => simp [pairing, appell, PseudoFiniteGramObstruction.expectation_one]
  | succ d ih =>
    rw [pair_recurrence, above_degree_zero a d (3*(d+1)+1) (by omega)]
    have hs : 3*(d+1)-3=3*d := by omega
    rw [hs, ih, zero_add]
    have hf : ((3*(d+1)).descFactorial 3 : ℝ)*((3*d).factorial : ℝ) =
        ((3*(d+1)).factorial : ℝ) := by
      have h := Nat.factorial_mul_descFactorial (show 3 ≤ 3*(d+1) by omega)
      rw [hs] at h
      rw [mul_comm] at h
      exact_mod_cast h
    rw [pow_succ]
    calc
      _ = (((3*(d+1)).descFactorial 3 : ℝ)*((3*d).factorial : ℝ)) *
          ((4*a)^d*(4*a)) := by ring
      _ = _ := by rw [hf]

theorem pairing_polynomial_sum (a : ℝ) (n : ℕ) (P : Polynomial ℝ) :
    pairing 4 a (appell a n) P = ∑ k ∈ Finset.range (P.natDegree+1),
      P.coeff k * pairing 4 a (appell a n) (X^k) := by
  calc
    _ = pairing 4 a (appell a n)
        (∑ k ∈ Finset.range (P.natDegree+1), P.coeff k • (X:Polynomial ℝ)^k) := by
      congr 1
      simpa only [smul_eq_C_mul] using P.as_sum_range_C_mul_X_pow
    _ = _ := by
      simp only [pairing, Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul]

theorem polynomial_above_degree_zero (a : ℝ) (P : Polynomial ℝ) (n : ℕ)
    (hn : 3*P.natDegree < n) : pairing 4 a (appell a n) P = 0 := by
  rw [pairing_polynomial_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [above_degree_zero a k n (by have := Finset.mem_range.mp hk; omega), mul_zero]

theorem polynomial_top_pairing (a : ℝ) (P : Polynomial ℝ) :
    pairing 4 a (appell a (3*P.natDegree)) P =
      P.leadingCoeff * ((3*P.natDegree).factorial : ℝ)*(4*a)^P.natDegree := by
  rw [pairing_polynomial_sum, Finset.sum_range_succ]
  have hz : ∑ k ∈ Finset.range P.natDegree,
      P.coeff k * pairing 4 a (appell a (3*P.natDegree)) (X^k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [above_degree_zero a k (3*P.natDegree)
      (by have := Finset.mem_range.mp hk; omega), mul_zero]
  rw [hz, zero_add, top_pairing, coeff_natDegree]
  ring

theorem polynomial_top_ne_zero (a : ℝ) (ha : a ≠ 0) (P : Polynomial ℝ) (hP : P ≠ 0) :
    pairing 4 a (appell a (3*P.natDegree)) P ≠ 0 := by
  rw [polynomial_top_pairing]
  exact mul_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr hP)
    (by exact_mod_cast Nat.factorial_ne_zero (3*P.natDegree)))
    (pow_ne_zero _ (mul_ne_zero (by norm_num) ha))

theorem full_pairing_nondegenerate (a : ℝ) (ha : a ≠ 0) (P : Polynomial ℝ)
    (h : ∀ Q : Polynomial ℝ, pairing 4 a Q P = 0) : P = 0 := by
  by_contra hP
  exact polynomial_top_ne_zero a ha P hP (h _)

end OperatorDerivativeRewrite.Foundation.QuarticAppellPairing
