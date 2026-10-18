import Foundation.HigherHeatPositionTransport

/-! Uniform position-norm estimates for every iterated native increment-coordinate derivative. -/
noncomputable section

namespace OperatorDerivativeRewrite.Foundation.HigherHeatPositionSteinDerivative
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatPositionTransport
open MultivariateFactorialDomain MultivariateDirectionalKernel

theorem coordinates_derivative (n : ℕ) (j : Fin (size n)) (P : Test n) :
    coordinates n (polynomialDerivative (direction (size n) j) P) =
      polynomialDerivative (Pi.single j 1) (coordinates n P) := by
  apply MvPolynomial.funext
  intro x
  have he := congrArg Polynomial.derivative (line_coordinates n j x P)
  rw [derivative_line, derivative_line] at he
  have hv := congrArg (fun Q : Polynomial ℝ => Q.eval 0) he
  simpa only [eval_line, zero_mul, add_zero, eval_coordinates] using hv.symm

theorem inverse_derivative (n : ℕ) (j : Fin (size n)) (P : Test n) :
    (coordinates n).symm (polynomialDerivative (Pi.single j 1) P) =
      polynomialDerivative (direction (size n) j) ((coordinates n).symm P) := by
  apply (coordinates n).injective
  rw [AlgEquiv.apply_symm_apply, coordinates_derivative, AlgEquiv.apply_symm_apply]

theorem inverse_iterate (n : ℕ) (j : Fin (size n)) (r : ℕ) (P : Test n) :
    (coordinates n).symm
      ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[r] P) =
      (polynomialDerivative (direction (size n) j) : Test n → Test n)^[r]
        ((coordinates n).symm P) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', inverse_derivative, ih,
      Function.iterate_succ_apply']

theorem encode_iterate_bound (n : ℕ) (j : Fin (size n)) (r : ℕ) (P : Test n) :
    ‖encode n ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[r] P)‖ ≤
      ‖encode n P‖ := by
  simp only [encode_apply]
  rw [inverse_iterate, ← derivative_iterate_core]
  simpa only [one_mul] using (derivative (direction (size n) j) (direction_bound (size n) j)^r).le_of_opNorm_le
    (derivative_power_norm _ _ r) _

end OperatorDerivativeRewrite.Foundation.HigherHeatPositionSteinDerivative
