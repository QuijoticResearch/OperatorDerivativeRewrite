import Foundation.HigherHeatPolynomialRealization

/-! Centered one-point marginals do not separate correction functions. -/
noncomputable section
open Polynomial
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.PseudoCorrectionObstruction
open PseudoPolynomialStein PseudoClarkOconeObstruction HigherHeatPolynomialRealization

theorem marginal_invisible_linear (p : ℕ) (hp : 1 < p) (c t : ℝ) :
    expectation p (c*t) X = 0 := linear_mean_zero p hp (c*t)

theorem marginals_do_not_separate (p : ℕ) (hp : 1 < p) (c : ℝ) :
    ∃ P : Polynomial ℝ, P ≠ 0 ∧ ∀ t : ℝ, expectation p (c*t) P = 0 :=
  ⟨X, X_ne_zero, fun t => marginal_invisible_linear p hp c t⟩

theorem actual_marginals_do_not_separate (m : ℕ) (hm : 0 < m) :
    ∃ P : Polynomial ℝ, P ≠ 0 ∧ ∀ (t : ℝ≥0) (ht : 0 < t),
      kernelExpectation m hm t ht P = 0 := by
  refine ⟨X, X_ne_zero, ?_⟩
  intro t ht
  rw [kernelExpectation_eq_moments]
  exact linear_mean_zero (2*m) (by omega) _

theorem indistinguishable_corrections (p : ℕ) (hp : 1 < p) (c : ℝ)
    (φ : Polynomial ℝ) :
    φ + X ≠ φ ∧ ∀ t : ℝ, expectation p (c*t) (φ+X) = expectation p (c*t) φ := by
  constructor
  · intro h
    have hx : (X : Polynomial ℝ)=0 := add_left_cancel (show φ+X=φ+0 by rw [h, add_zero])
    exact X_ne_zero hx
  · intro t
    rw [map_add, marginal_invisible_linear p hp, add_zero]

end OperatorDerivativeRewrite.Foundation.PseudoCorrectionObstruction
