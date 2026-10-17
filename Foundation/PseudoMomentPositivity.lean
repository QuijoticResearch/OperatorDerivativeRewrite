import Foundation.ManuscriptSchurDiagnostics

/-! A polynomial square obstruction for every pure pseudo-moment order p > 2.
Indefinite algebraic pairings and their non-degeneracy are separate questions. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PseudoMomentPositivity
open Polynomial

theorem square_pairing_expansion (E : Polynomial ℝ →ₗ[ℝ] ℝ)
    (P Q : Polynomial ℝ) (a : ℝ) :
    E ((P + a • Q)^2) = E (P^2) + 2*a*E (P*Q) + a^2*E (Q^2) := by
  have he : (P + a • Q)^2 = P^2 + (2*a) • (P*Q) + a^2 • Q^2 := by
    simp only [Algebra.smul_def, map_mul, map_pow, map_ofNat]
    ring
  rw [he, map_add, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]

/-- A nonzero off-diagonal pairing between two null squares gives a negative square. -/
theorem two_null_squares_witness (E : Polynomial ℝ →ₗ[ℝ] ℝ)
    (P Q : Polynomial ℝ) (hP : E (P^2) = 0) (hQ : E (Q^2) = 0) :
    E ((P - E (P*Q) • Q)^2) = -2 * E (P*Q)^2 := by
  rw [sub_eq_add_neg, ← neg_smul, square_pairing_expansion, hP, hQ]
  ring

theorem two_null_squares_positive_witness (E : Polynomial ℝ →ₗ[ℝ] ℝ)
    (P Q : Polynomial ℝ) (hP : E (P^2) = 0) (hQ : E (Q^2) = 0) :
    E ((P + E (P*Q) • Q)^2) = 2 * E (P*Q)^2 := by
  rw [square_pairing_expansion, hP, hQ]
  ring

/-- Null diagonal values of an indefinite pairing cannot be quotiented as a linear kernel. -/
theorem null_squares_not_additive (E : Polynomial ℝ →ₗ[ℝ] ℝ)
    (P Q : Polynomial ℝ) (hP : E (P^2) = 0) (hQ : E (Q^2) = 0)
    (hPQ : E (P*Q) ≠ 0) : E ((P+Q)^2) ≠ 0 := by
  have he := square_pairing_expansion E P Q 1
  simp only [one_smul, hP, hQ, one_pow, zero_add, mul_zero, add_zero] at he
  rw [he]
  exact mul_ne_zero (by norm_num) hPQ

theorem two_null_squares_not_positive (E : Polynomial ℝ →ₗ[ℝ] ℝ)
    (P Q : Polynomial ℝ) (hP : E (P^2) = 0) (hQ : E (Q^2) = 0)
    (hPQ : E (P*Q) ≠ 0) : ¬ ∀ R : Polynomial ℝ, 0 ≤ E (R^2) := by
  intro hpos
  have h := hpos (P - E (P*Q) • Q)
  rw [two_null_squares_witness E P Q hP hQ] at h
  nlinarith [sq_pos_of_ne_zero hPQ]

theorem pure_order_nondiagonal_degrees (p : ℕ) (hp : 2 < p) :
    ¬ p ∣ 2 ∧ ¬ p ∣ 2*(p-1) := by
  refine ⟨Nat.not_dvd_of_pos_of_lt (by omega) hp, ?_⟩
  rintro ⟨k, hk⟩
  have hprev : p-1+1 = p := by omega
  have hklt : k < 2 := by nlinarith
  have hkpos : 0 < k := by nlinarith
  have hkone : k = 1 := by omega
  rw [hkone, mul_one] at hk
  omega

/-- The obstruction depends only on the stated moments, with either sign of the leading one. -/
theorem pure_order_negative_square (E : Polynomial ℝ →ₗ[ℝ] ℝ)
    (p : ℕ) (hp : 2 < p)
    (hzero : ∀ n : ℕ, ¬ p ∣ n → E (X^n) = 0) :
    E ((X - E (X^p) • X^(p-1))^2) = -2 * E (X^p)^2 := by
  have hcross : (X : Polynomial ℝ) * X^(p-1) = X^p := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hQ : E (((X : Polynomial ℝ)^(p-1))^2) = 0 := by
    rw [← pow_mul, Nat.mul_comm (p-1) 2]
    exact hzero _ (pure_order_nondiagonal_degrees p hp).2
  simpa only [hcross] using two_null_squares_witness E X (X^(p-1))
    (hzero 2 (pure_order_nondiagonal_degrees p hp).1) hQ

theorem pure_order_not_square_positive (E : Polynomial ℝ →ₗ[ℝ] ℝ)
    (p : ℕ) (hp : 2 < p)
    (hzero : ∀ n : ℕ, ¬ p ∣ n → E (X^n) = 0)
    (hlead : E (X^p) ≠ 0) : ¬ ∀ R : Polynomial ℝ, 0 ≤ E (R^2) := by
  intro hpos
  have h := hpos (X - E (X^p) • X^(p-1))
  rw [pure_order_negative_square E p hp hzero] at h
  nlinarith [sq_pos_of_ne_zero hlead]

/-- The manuscript's factorial leading moment is nonzero for every nonzero coefficient. -/
theorem factorial_pseudo_moments_not_positive (E : Polynomial ℝ →ₗ[ℝ] ℝ)
    (p : ℕ) (hp : 2 < p) (c T : ℝ) (hc : c ≠ 0) (hT : 0 < T)
    (hzero : ∀ n : ℕ, ¬ p ∣ n → E (X^n) = 0)
    (hlead : E (X^p) = (p.factorial : ℝ)*c*T) :
    ¬ ∀ R : Polynomial ℝ, 0 ≤ E (R^2) := by
  apply pure_order_not_square_positive E p hp hzero
  rw [hlead]
  exact mul_ne_zero (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero p) hc)
    (ne_of_gt hT)

/-- For Airy moments, a degree-two polynomial already has a negative square pairing. -/
theorem airy_negative_square (E : Polynomial ℝ →ₗ[ℝ] ℝ) (T : ℝ)
    (h2 : E (X^2) = 0) (h3 : E (X^3) = -6*T) (h4 : E (X^4) = 0) :
    E ((X + (6*T) • X^2)^2) = -72*T^2 := by
  rw [square_pairing_expansion]
  have hcross : (X : Polynomial ℝ) * X^2 = X^3 := by ring
  have hsq : ((X : Polynomial ℝ)^2)^2 = X^4 := by ring
  rw [hcross, hsq, h2, h3, h4]
  ring

end OperatorDerivativeRewrite.Foundation.PseudoMomentPositivity
