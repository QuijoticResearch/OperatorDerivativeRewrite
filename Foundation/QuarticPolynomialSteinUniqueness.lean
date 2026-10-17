import Foundation.QuarticAppellDualDensity

/-! Polynomial-test Stein uniqueness and a polynomial-test first-order obstruction. -/
noncomputable section
open Polynomial
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.QuarticPolynomialSteinUniqueness
open PseudoPolynomialStein PseudoClarkOconeObstruction QuarticAppellPairing

theorem canonical_weight (a : ℝ) (ha : a ≠ 0) (P : Polynomial ℝ) :
    expectation 4 a (P * ((4*a)⁻¹ • (X:Polynomial ℝ))) =
      expectation 4 a (derivative^[3] P) := by
  rw [mul_smul_comm, map_smul, mul_comm P X, polynomial_stein]
  simp only [smul_eq_mul]
  field_simp
  norm_num

theorem polynomial_weight_unique (a : ℝ) (ha : a ≠ 0) (W : Polynomial ℝ)
    (h : ∀ P : Polynomial ℝ, expectation 4 a (P*W) =
      expectation 4 a (derivative^[3] P)) : W = (4*a)⁻¹ • (X:Polynomial ℝ) := by
  apply sub_eq_zero.mp
  apply full_pairing_nondegenerate a ha
  intro P
  rw [pairing, mul_sub, map_sub, h P, canonical_weight a ha P, sub_self]

theorem no_first_order_polynomial_weight (a : ℝ) (ha : a ≠ 0) :
    ¬ ∃ W : Polynomial ℝ, ∀ P : Polynomial ℝ,
      expectation 4 a (P*W) = expectation 4 a P.derivative := by
  rintro ⟨W, hW⟩
  apply QuarticAppellDualDensity.coordinate_one_not_polynomial_pairing a ha
  refine ⟨W, fun P => ?_⟩
  rw [pairing, hW, QuarticAppellExpansion.coordinate_apply]
  simp

theorem actual_polynomial_weight_unique (t : ℝ≥0) (ht : 0 < t) (W : Polynomial ℝ)
    (h : ∀ P : Polynomial ℝ,
      HigherHeatPolynomialRealization.kernelExpectation 2 (by norm_num) t ht (P*W) =
      HigherHeatPolynomialRealization.kernelExpectation 2 (by norm_num) t ht
        (derivative^[3] P)) : W = (-4*(t:ℝ))⁻¹ • (X:Polynomial ℝ) := by
  have hne : (-(t:ℝ)) ≠ 0 := neg_ne_zero.mpr (ne_of_gt (by exact_mod_cast ht))
  have hw := polynomial_weight_unique (-(t:ℝ)) hne W (by
    intro P
    have hp := h P
    simp only [HigherHeatPolynomialRealization.kernelExpectation_eq_moments] at hp
    norm_num at hp
    exact hp)
  simpa only [mul_neg, neg_mul] using hw

theorem actual_no_first_order_polynomial_weight (t : ℝ≥0) (ht : 0 < t) :
    ¬ ∃ W : Polynomial ℝ, ∀ P : Polynomial ℝ,
      HigherHeatPolynomialRealization.kernelExpectation 2 (by norm_num) t ht (P*W) =
      HigherHeatPolynomialRealization.kernelExpectation 2 (by norm_num) t ht P.derivative := by
  rintro ⟨W, hW⟩
  apply no_first_order_polynomial_weight (-(t:ℝ))
    (neg_ne_zero.mpr (ne_of_gt (by exact_mod_cast ht)))
  refine ⟨W, fun P => ?_⟩
  have hp := hW P
  simp only [HigherHeatPolynomialRealization.kernelExpectation_eq_moments] at hp
  norm_num at hp
  exact hp

end OperatorDerivativeRewrite.Foundation.QuarticPolynomialSteinUniqueness
