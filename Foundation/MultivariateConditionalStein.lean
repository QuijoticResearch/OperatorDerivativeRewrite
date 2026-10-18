import Foundation.SingleCoordinateConditioning

/-! Native coordinate Stein identity derived from actual conditional polynomial expectations. -/
noncomputable section
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MultivariateConditionalStein
open SingleCoordinateConditioning MultivariateDirectionalKernel MultivariateFactorialDomain
open PureOrderPolynomialConditioning HigherHeatMultivariateMoments
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem conditioning_eval (p : ℕ) (a : ι → ℝ) (j : ι) (x : ι → ℝ)
    (P : MvPolynomial ι ℝ) :
    MvPolynomial.eval x (conditioning p a (Finset.univ.erase j) P) =
      PseudoPolynomialStein.expectation p (a j) (line (Pi.single j 1) (eraseValue j x) P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [conditioning_monomial_eval, line_monomial, PseudoPolynomialStein.expectation_monomial]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem conditioning_stein (p : ℕ) (a : ι → ℝ) (j : ι) (P : MvPolynomial ι ℝ) :
    conditioning p a (Finset.univ.erase j) (MvPolynomial.X j * P) =
      ((p:ℝ)*a j) • conditioning p a (Finset.univ.erase j)
        ((polynomialDerivative (Pi.single j 1) : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[p-1] P) := by
  apply MvPolynomial.funext
  intro x
  rw [conditioning_eval, MvPolynomial.smul_eval, conditioning_eval, map_mul, line_X]
  simp only [eraseValue, Function.update_self, Pi.single_eq_same, Polynomial.C_0,
    Polynomial.C_1, one_mul, zero_add]
  rw [PseudoPolynomialStein.polynomial_stein, iterate_derivative_line]

theorem actual_coordinate_stein (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (j : ι) (P : MvPolynomial ι ℝ) :
    mean m hm t ht (MvPolynomial.X j * P) =
      (((2*m:ℕ):ℝ)*parameters m t j) • mean m hm t ht
        ((polynomialDerivative (Pi.single j 1) : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[2*m-1] P) := by
  have he := actual_mean_conditioning m hm t ht (Finset.univ.erase j) (MvPolynomial.X j * P)
  rw [conditioning_stein, map_smul, actual_mean_conditioning] at he
  exact he.symm

end OperatorDerivativeRewrite.Foundation.MultivariateConditionalStein
