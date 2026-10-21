import Foundation.HigherHeatFourthChannelSteps
import Foundation.HigherHeatCubicRemainder

/-! Exact signed fourth increment identity, including its genuine drift channel. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatQuarticStepIdentity
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement HigherHeatSecondChannelSteps
open HigherHeatThirdChannelSteps HigherHeatFourthChannelSteps HigherHeatCubicStepIdentity
open HigherHeatPairedDualCausality MultivariateFactorialDomain MultivariateFactorialSubstitution
open HigherHeatAdaptedStepDuality

theorem derivative_cube_missing (n : ℕ) (j : Fin (size n)) (F : Test n)
    (hF : j ∉ F.vars) :
    polynomialDerivative (Pi.single j 1) (F*(MvPolynomial.X j)^3) =
      F*(MvPolynomial.X j)^2 + F*(MvPolynomial.X j)^2 + F*(MvPolynomial.X j)^2 := by
  have hD := derivative_zero_of_missing j F hF
  have hp (A B : Test n) : polynomialDerivative (Pi.single j 1) (A*B) =
      A*polynomialDerivative (Pi.single j 1) B +
        B*polynomialDerivative (Pi.single j 1) A := by
    simpa only [smul_eq_mul] using Derivation.leibniz (polynomialDerivative (Pi.single j 1)) A B
  simp only [show (MvPolynomial.X j : Test n)^3 =
      MvPolynomial.X j * (MvPolynomial.X j * MvPolynomial.X j) by ring,
    hp, hD, polynomialDerivative_X, Pi.single_eq_same, MvPolynomial.C_1]
  ring

theorem quartic_step_dual (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    pairing 2 (by norm_num) T hT (core (cylinderOf n (F*(MvPolynomial.X j)^4))) =
      firstChannel 2 T (coefficientField n 2 (by norm_num) T hT j (F*(MvPolynomial.X j)^3)) +
      (3:ℕ) • secondChannel 2 T
        (coefficientField n 2 (by norm_num) T hT j (F*(MvPolynomial.X j)^2)) +
      (3:ℕ) • thirdChannel T (coefficientField n 2 (by norm_num) T hT j (F*MvPolynomial.X j)) +
      fourthChannel T (coefficientField n 2 (by norm_num) T hT j F) := by
  have hx : polynomialDerivative (Pi.single j 1) (F*MvPolynomial.X j) = F := by
    rw [Derivation.leibniz, derivative_zero_of_missing j F hF, polynomialDerivative_X]
    simp only [Pi.single_eq_same, MvPolynomial.C_1, smul_eq_mul, mul_one, mul_zero, add_zero]
  have he := agreement_dual n T hT j (F*(MvPolynomial.X j)^3)
  have hp : (F*(MvPolynomial.X j)^3)*MvPolynomial.X j = F*(MvPolynomial.X j)^4 := by ring
  rw [hp] at he
  simp only [correction, quadraticCorrection, Function.iterate_succ_apply', Function.iterate_zero,
    id_eq, derivative_cube_missing n j F hF, map_add, derivative_square_missing n j F hF,
    hx, coefficientField_add] at he
  rw [he]
  apply ContinuousLinearMap.ext
  intro G
  simp only [add_apply, smul_apply, nsmul_eq_mul, smul_eq_mul]
  norm_num
  ring

end OperatorDerivativeRewrite.Foundation.HigherHeatQuarticStepIdentity
