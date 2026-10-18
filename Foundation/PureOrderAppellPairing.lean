import Foundation.PureOrderAppellExpansion

/-! The highest nonzero Appell pairing with monomials, without a global dual assumption. -/
noncomputable section
open Polynomial
namespace OperatorDerivativeRewrite.Foundation.PureOrderAppellPairing
open PureOrderAppellCalculus PseudoPolynomialStein PseudoClarkOconeObstruction

theorem appell_iterate (p : ℕ) (a : ℝ) (k n : ℕ) :
    derivative^[k] (appell p a n) = (n.descFactorial k : ℝ) • appell p a (n-k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp [appell, iterate_derivative_one (Nat.zero_lt_succ k)]
    | succ n =>
      rw [Function.iterate_succ_apply, appell_derivative, iterate_derivative_smul,
        ih, Nat.succ_descFactorial_succ, Nat.cast_mul, smul_smul, Nat.succ_sub_succ]
      norm_cast

theorem pair_recurrence (p : ℕ) (a : ℝ) (n d : ℕ) :
    pairing p a (appell p a n) (X^(d+1)) =
      pairing p a (appell p a (n+1)) (X^d) +
      ((p:ℝ) * a*(n.descFactorial (p - 1) : ℝ)) * pairing p a (appell p a (n-(p - 1))) (X^d) := by
  have hx : appell p a n * X^(d+1) = appell p a (n+1) * X^d +
      ((p:ℝ) * a*(n.descFactorial (p - 1) : ℝ)) • (appell p a (n-(p - 1)) * X^d) := by
    rw [appell, raise, appell_iterate, smul_smul]
    simp only [smul_eq_C_mul, map_mul]
    ring
  simp only [pairing]
  rw [hx, map_add, map_smul]
  rfl

theorem above_degree_zero (p : ℕ) (a : ℝ) (d n : ℕ) (hn : (p - 1) * d < n) :
    pairing p a (appell p a n) (X^d) = 0 := by
  induction d generalizing n with
  | zero =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa only [pairing, pow_zero, mul_one] using appell_mean_zero p a k
  | succ d ih =>
    have hs : (p - 1) * (d+1)=(p - 1) * d+(p - 1) := by ring
    rw [pair_recurrence, ih (n+1) (by omega), ih (n-(p - 1)) (by omega)]
    ring

theorem top_pairing (p : ℕ) (a : ℝ) (d : ℕ) :
    pairing p a (appell p a ((p - 1) * d)) (X^d) =
      (((p - 1) * d).factorial : ℝ) * ((p:ℝ) * a)^d := by
  induction d with
  | zero => simp [pairing, appell, PseudoFiniteGramObstruction.expectation_one]
  | succ d ih =>
    rw [pair_recurrence, above_degree_zero p a d ((p - 1) * (d+1)+1) (by nlinarith)]
    have hs : (p - 1) * (d+1)-(p - 1)=(p - 1) * d := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel_right]
    rw [hs, ih, zero_add]
    have hf : (((p - 1) * (d+1)).descFactorial (p - 1) : ℝ) * (((p - 1) * d).factorial : ℝ) =
        (((p - 1) * (d+1)).factorial : ℝ) := by
      have h := Nat.factorial_mul_descFactorial (show (p - 1) ≤ (p - 1) * (d+1) by nlinarith)
      rw [hs] at h
      rw [mul_comm] at h
      exact_mod_cast h
    rw [pow_succ]
    calc
      _ = ((((p - 1) * (d+1)).descFactorial (p - 1) : ℝ) * (((p - 1) * d).factorial : ℝ)) *
          (((p:ℝ) * a)^d*((p:ℝ) * a)) := by ring
      _ = _ := by rw [hf]

theorem pairing_polynomial_sum (p : ℕ) (a : ℝ) (n : ℕ) (P : Polynomial ℝ) :
    pairing p a (appell p a n) P = ∑ k ∈ Finset.range (P.natDegree+1),
      P.coeff k * pairing p a (appell p a n) (X^k) := by
  calc
    _ = pairing p a (appell p a n)
        (∑ k ∈ Finset.range (P.natDegree+1), P.coeff k • (X:Polynomial ℝ)^k) := by
      congr 1
      simpa only [smul_eq_C_mul] using P.as_sum_range_C_mul_X_pow
    _ = _ := by
      simp only [pairing, Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul]

theorem polynomial_above_degree_zero (p : ℕ) (a : ℝ) (P : Polynomial ℝ) (n : ℕ)
    (hn : (p - 1) * P.natDegree < n) : pairing p a (appell p a n) P = 0 := by
  rw [pairing_polynomial_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [above_degree_zero p a k n (by have := Finset.mem_range.mp hk; nlinarith), mul_zero]

theorem polynomial_top_pairing (p : ℕ) (hp : 1 < p) (a : ℝ) (P : Polynomial ℝ) :
    pairing p a (appell p a ((p - 1) * P.natDegree)) P =
      P.leadingCoeff * (((p - 1) * P.natDegree).factorial : ℝ) * ((p:ℝ) * a)^P.natDegree := by
  rw [pairing_polynomial_sum, Finset.sum_range_succ]
  have hz : ∑ k ∈ Finset.range P.natDegree,
      P.coeff k * pairing p a (appell p a ((p - 1) * P.natDegree)) (X^k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [above_degree_zero p a k ((p - 1) * P.natDegree)
      (by exact Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hk) (by omega)), mul_zero]
  rw [hz, zero_add, top_pairing p, coeff_natDegree]
  ring

theorem polynomial_top_ne_zero (p : ℕ) (hp : 1 < p) (a : ℝ) (ha : a ≠ 0)
    (P : Polynomial ℝ) (hP : P ≠ 0) :
    pairing p a (appell p a ((p - 1) * P.natDegree)) P ≠ 0 := by
  rw [polynomial_top_pairing p hp]
  exact mul_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr hP)
    (by exact_mod_cast Nat.factorial_ne_zero ((p - 1) * P.natDegree)))
    (pow_ne_zero _ (mul_ne_zero (by exact_mod_cast (ne_of_gt (show 0 < p by omega))) ha))

theorem full_pairing_nondegenerate (p : ℕ) (hp : 1 < p) (a : ℝ) (ha : a ≠ 0) (P : Polynomial ℝ)
    (h : ∀ Q : Polynomial ℝ, pairing p a Q P = 0) : P = 0 := by
  by_contra hP
  exact polynomial_top_ne_zero p hp a ha P hP (h _)

end OperatorDerivativeRewrite.Foundation.PureOrderAppellPairing
