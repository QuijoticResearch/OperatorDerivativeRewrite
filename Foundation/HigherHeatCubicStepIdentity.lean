import Foundation.HigherHeatThirdChannelSteps
import Foundation.HigherHeatQuadraticChannelLimit

/-! Exact signed cubic increment identity on the completed analytic test dual.
All three channels occur. This is not yet a universal chronological formula. -/
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCubicStepIdentity
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatWeakTimeAdjoint HigherHeatWeakStepFields HigherHeatDyadicStepAgreement
open HigherHeatCompletedPairing HigherHeatSecondChannelSteps HigherHeatThirdChannelSteps
open HigherHeatPairedDualCausality MultivariateFactorialDomain MultivariateFactorialSubstitution
open HigherHeatAdaptedStepDuality

theorem coefficientField_add (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F G : Test n) :
    coefficientField n m hm T hT j (F+G) =
      coefficientField n m hm T hT j F + coefficientField n m hm T hT j G := by
  unfold coefficientField HigherHeatWeakStepFields.step
  rw [map_add, map_add, map_add]
  exact MeasureTheory.indicatorConstLp_add.symm

theorem derivative_square_missing (n : ℕ) (j : Fin (size n)) (F : Test n)
    (hF : j ∉ F.vars) :
    polynomialDerivative (Pi.single j 1) (F*(MvPolynomial.X j)^2) =
      F*MvPolynomial.X j + F*MvPolynomial.X j := by
  have hD := derivative_zero_of_missing j F hF
  have hp (A B : Test n) : polynomialDerivative (Pi.single j 1) (A*B) =
      A*polynomialDerivative (Pi.single j 1) B +
        B*polynomialDerivative (Pi.single j 1) A := by
    simpa only [smul_eq_mul] using Derivation.leibniz (polynomialDerivative (Pi.single j 1)) A B
  rw [pow_two, hp, hp, hD, polynomialDerivative_X]
  simp only [Pi.single_eq_same, MvPolynomial.C_1]
  ring

theorem cubic_step_dual (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    pairing 2 (by norm_num) T hT (core (cylinderOf n (F*(MvPolynomial.X j)^3))) =
      firstChannel 2 T (coefficientField n 2 (by norm_num) T hT j (F*(MvPolynomial.X j)^2)) +
      secondChannel 2 T (coefficientField n 2 (by norm_num) T hT j (F*MvPolynomial.X j)) +
      secondChannel 2 T (coefficientField n 2 (by norm_num) T hT j (F*MvPolynomial.X j)) +
      thirdChannel T (coefficientField n 2 (by norm_num) T hT j F) := by
  have hD := derivative_zero_of_missing j F hF
  have hx : polynomialDerivative (Pi.single j 1) (F*MvPolynomial.X j) = F := by
    rw [Derivation.leibniz, hD, polynomialDerivative_X]
    simp only [Pi.single_eq_same, MvPolynomial.C_1, smul_eq_mul, mul_one, mul_zero, add_zero]
  have hxx := derivative_square_missing n j F hF
  have hthree : (polynomialDerivative (Pi.single j 1) : Test n → Test n)^[3]
      (F*(MvPolynomial.X j)^2) = 0 := by
    change polynomialDerivative (Pi.single j 1) (polynomialDerivative (Pi.single j 1)
      (polynomialDerivative (Pi.single j 1) (F*(MvPolynomial.X j)^2))) = 0
    rw [hxx, map_add, hx, map_add, hD, zero_add]
  have he := quadratic_agreement_dual n T hT j (F*(MvPolynomial.X j)^2) hthree
  simp only [hxx, map_add, hx, coefficientField_add] at he
  have hp : (F*(MvPolynomial.X j)^2)*MvPolynomial.X j = F*(MvPolynomial.X j)^3 := by ring
  rw [hp] at he
  rw [he]
  apply ContinuousLinearMap.ext
  intro G
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem cubic_step_actual (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) (G : Cylinder) :
    ((firstChannel 2 T (coefficientField n 2 (by norm_num) T hT j (F*(MvPolynomial.X j)^2))
          (core G) +
      secondChannel 2 T (coefficientField n 2 (by norm_num) T hT j (F*MvPolynomial.X j))
          (core G) +
      secondChannel 2 T (coefficientField n 2 (by norm_num) T hT j (F*MvPolynomial.X j))
          (core G) +
      thirdChannel T (coefficientField n 2 (by norm_num) T hT j F) (core G) : ℝ) : ℂ) =
      cylindricalExpectation 2 (by norm_num) T hT (cylinderOf n (F*(MvPolynomial.X j)^3)*G) := by
  have he := congrArg (fun φ : Dual => (φ (core G) : ℂ)) (cubic_step_dual n T hT j F hF)
  exact he.symm.trans (pairing_core_complex 2 (by norm_num) T hT _ G)

end OperatorDerivativeRewrite.Foundation.HigherHeatCubicStepIdentity
