import Foundation.PureOrderConditionalPairing
import Foundation.HigherHeatCylindricalConditioning

/-! Actual signed polynomial cylinder projections are symmetric for expectation pairing. -/
noncomputable section
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.HigherHeatCausalPairing
open HigherHeatPolynomialCylinders HigherHeatCylindricalConditioning
open HigherHeatDyadicConditioning PureOrderConditionalPairing

theorem cylinder_projection_symmetric (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b))) (F G : Cylinder) :
    cylindricalExpectation m hm T hT (projection m hm T hT b S F * G) =
      cylindricalExpectation m hm T hT (F * projection m hm T hT b S G) := by
  apply tail_induction b (fun F =>
    cylindricalExpectation m hm T hT (projection m hm T hT b S F * G) =
      cylindricalExpectation m hm T hT (F * projection m hm T hT b S G)) _ F
  intro n hn P
  apply tail_induction n (fun G =>
    cylindricalExpectation m hm T hT (projection m hm T hT b S (cylinderOf n P) * G) =
      cylindricalExpectation m hm T hT (cylinderOf n P * projection m hm T hT b S G)) _ G
  intro k hnk Q
  rw [← cylinder_refinement n k hnk P]
  rw [projection_apply m hm T hT b S k (hn.trans hnk),
    projection_apply m hm T hT b S k (hn.trans hnk),
    ← map_mul (cylinderOf k), ← map_mul (cylinderOf k),
    cylindricalExpectation_apply, cylindricalExpectation_apply]
  exact actual_pair_symmetric m hm _ _ _ (transfer n k hnk P) Q

end OperatorDerivativeRewrite.Foundation.HigherHeatCausalPairing
