import Foundation.PureOrderAppellPairing

/-! Full pure-order polynomial Stein uniqueness; coordinate duals need a larger space. -/
noncomputable section
open Polynomial
namespace OperatorDerivativeRewrite.Foundation.PureOrderSteinUniqueness
open PureOrderAppellCalculus PureOrderAppellExpansion PureOrderAppellPairing
open PseudoPolynomialStein PseudoClarkOconeObstruction

theorem canonical_weight (p : ℕ) (hp : 0 < p) (a : ℝ) (ha : a ≠ 0) (P : Polynomial ℝ) :
    expectation p a (P * (((p:ℝ)*a)⁻¹ • (X:Polynomial ℝ))) =
      expectation p a (derivative^[p-1] P) := by
  rw [mul_smul_comm, map_smul, mul_comm P X, polynomial_stein]
  simp only [smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero (by exact_mod_cast (ne_of_gt hp)) ha), one_mul]

theorem polynomial_weight_unique (p : ℕ) (hp : 1 < p) (a : ℝ) (ha : a ≠ 0)
    (W : Polynomial ℝ) (h : ∀ P : Polynomial ℝ, expectation p a (P*W) =
      expectation p a (derivative^[p-1] P)) : W = ((p:ℝ)*a)⁻¹ • (X:Polynomial ℝ) := by
  apply sub_eq_zero.mp
  apply full_pairing_nondegenerate p hp a ha
  intro P
  rw [pairing, mul_sub, map_sub, h P, canonical_weight p (by omega) a ha P, sub_self]

theorem no_polynomial_dual_one (p : ℕ) (hp : 2 < p) (a : ℝ) (ha : a ≠ 0) :
    ¬ ∃ Q : Polynomial ℝ, ∀ n : ℕ,
      pairing p a (appell p a n) Q = if n=1 then 1 else 0 := by
  rintro ⟨Q,hQ⟩
  have hn : Q ≠ 0 := by
    intro hz
    have h := hQ 1
    simp [hz, pairing] at h
  have h := polynomial_top_ne_zero p (by omega) a ha Q hn
  apply h
  have hi : (p-1)*Q.natDegree ≠ 1 := by
    intro he
    have hd := dvd_mul_right (p-1) Q.natDegree
    rw [he] at hd
    have := Nat.le_of_dvd (by omega : 0 < (1:ℕ)) hd
    omega
  rw [hQ, ite_eq_right hi]

theorem coordinate_one_not_polynomial_pairing (p : ℕ) (hp : 2 < p) (a : ℝ) (ha : a ≠ 0) :
    ¬ ∃ Q : Polynomial ℝ, ∀ P : Polynomial ℝ,
      pairing p a P Q = coordinate p a 1 P := by
  rintro ⟨Q,hQ⟩
  apply no_polynomial_dual_one p hp a ha
  refine ⟨Q, fun n => ?_⟩
  rw [hQ, coordinate_appell]

theorem no_first_order_polynomial_weight (p : ℕ) (hp : 2 < p) (a : ℝ) (ha : a ≠ 0) :
    ¬ ∃ W : Polynomial ℝ, ∀ P : Polynomial ℝ,
      expectation p a (P*W) = expectation p a P.derivative := by
  rintro ⟨W,hW⟩
  apply coordinate_one_not_polynomial_pairing p hp a ha
  refine ⟨W, fun P => ?_⟩
  rw [pairing, hW, coordinate_apply]
  simp

end OperatorDerivativeRewrite.Foundation.PureOrderSteinUniqueness
