import Foundation.FiniteCoordinateConditioning
import Foundation.HigherHeatPolynomialCoordinates

/-! Actual finite signed conditioning and its uniform position-coordinate bound. -/
noncomputable section
open scoped NNReal BigOperators

namespace OperatorDerivativeRewrite.Foundation.HigherHeatPositionTransport
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatPositionVariation
open HigherHeatCylinderFourier MultivariateDirectionalKernel MultivariateFactorialDomain
open MultivariateFactorialHeat FiniteCoordinateConditioning

def direction (N : ℕ) (j i : Fin N) : ℝ := if j ≤ i then 1 else 0

theorem direction_bound (N : ℕ) (j i : Fin N) : |direction N j i| ≤ 1 := by
  simp only [direction]
  split <;> norm_num

theorem cumulative_axis (N : ℕ) (j : Fin N) :
    cumulativeEquiv N (Pi.single j (1:ℝ)) = direction N j := by
  funext i
  rw [cumulativeEquiv_apply]
  simp [linearImage, Pi.single_apply, cumulativeMatrix, direction]

theorem cumulative_line (N : ℕ) (j : Fin N) (x : Fin N → ℝ) (z : ℝ) :
    cumulativeEquiv N (fun i => x i + z*(Pi.single j (1:ℝ) : Fin N → ℝ) i) =
      fun i => cumulativeEquiv N x i + z*direction N j i := by
  have hx : (fun i => x i + z*(Pi.single j (1:ℝ) : Fin N → ℝ) i) =
      x + z • (Pi.single j (1:ℝ) : Fin N → ℝ) := rfl
  rw [hx]
  rw [map_add, map_smul, cumulative_axis]
  rfl

theorem line_coordinates (n : ℕ) (j : Fin (size n)) (x : Fin (size n) → ℝ) (P : Test n) :
    line (Pi.single j 1) x (coordinates n P) =
      line (direction (size n) j) (cumulativeEquiv (size n) x) P := by
  apply Polynomial.funext
  intro z
  rw [eval_line, eval_coordinates, eval_line, cumulative_line]

theorem coordinates_transport (n p : ℕ) (hp : 0 < p) (a : ℝ) (j : Fin (size n)) (P : Test n) :
    coordinates n (transport p hp a (direction (size n) j) P) =
      transport p hp a (Pi.single j 1) (coordinates n P) := by
  apply MvPolynomial.funext
  intro x
  rw [eval_coordinates]
  change MvPolynomial.eval (cumulativeEquiv (size n) x)
      (polynomialEvolution p a (direction (size n) j) P) =
    MvPolynomial.eval x (polynomialEvolution p a (Pi.single j 1) (coordinates n P))
  rw [← expectation_polynomialEvolution p hp, ← expectation_polynomialEvolution p hp,
    line_coordinates]

theorem inverse_transport (n p : ℕ) (hp : 0 < p) (a : ℝ) (j : Fin (size n)) (P : Test n) :
    (coordinates n).symm (transport p hp a (Pi.single j 1) P) =
      transport p hp a (direction (size n) j) ((coordinates n).symm P) := by
  apply (coordinates n).injective
  rw [AlgEquiv.apply_symm_apply, coordinates_transport, AlgEquiv.apply_symm_apply]

theorem evolution_encode (n p : ℕ) (hp : 0 < p) (a : ℝ) (j : Fin (size n)) (P : Test n) :
    evolution p a (direction (size n) j) (direction_bound (size n) j) (encode n P) =
      encode n (transport p hp a (Pi.single j 1) P) := by
  rw [encode_apply, encode_apply, inverse_transport]
  exact completed_transport p hp _ _ _ _

end OperatorDerivativeRewrite.Foundation.HigherHeatPositionTransport
