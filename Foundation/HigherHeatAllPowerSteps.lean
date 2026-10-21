import Foundation.HigherHeatAllProductChannels
import Foundation.HigherHeatMonomialJets
import Foundation.HigherHeatCubicStepIdentity

/-! Exact completed-dual identities for every native signed increment power
and every even heat order. Current-increment correction fields may anticipate. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAllPowerSteps
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatWeakStepFields HigherHeatDyadicStepAgreement
open HigherHeatAllProductChannels HigherHeatMonomialJets HigherHeatCubicStepIdentity
open HigherHeatAdaptedStepDuality HigherHeatPairedDualCausality
open MultivariateFactorialDomain MultivariateFactorialSubstitution

theorem coefficientField_nsmul (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (k : ℕ) :
    coefficientField n m hm T hT j (k • F) = k • coefficientField n m hm T hT j F := by
  induction k with
  | zero =>
    simp only [zero_nsmul]
    apply norm_eq_zero.mp
    rw [coefficientField, step_norm]
    simp
  | succ k ih => rw [succ_nsmul, coefficientField_add, ih, succ_nsmul]

theorem increment_power_jets (n : ℕ) (j : Fin (size n)) (F : Test n)
    (hF : j ∉ F.vars) (r k : ℕ) :
    (polynomialDerivative (Pi.single j 1) : Test n → Test n)^[k] (F*(MvPolynomial.X j)^r) =
      r.descFactorial k • (F*(MvPolynomial.X j)^(r-k)) := by
  apply derivative_iterate_mul_power _ F (MvPolynomial.X j)
    (derivative_zero_of_missing j F hF)
  simp only [polynomialDerivative_X, Pi.single_eq_same, MvPolynomial.C_1]

theorem power_step_dual (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) (r : ℕ) :
    pairing m hm T hT (core (cylinderOf n (F*(MvPolynomial.X j)^(r+1)))) =
      ∑ k ∈ Finset.range (2*m), r.descFactorial k • productChannel m T k
        (coefficientField n m hm T hT j (F*(MvPolynomial.X j)^(r-k))) := by
  have he := agreement_dual n m hm T hT j (F*(MvPolynomial.X j)^r)
  have hp : (F*(MvPolynomial.X j)^r)*MvPolynomial.X j = F*(MvPolynomial.X j)^(r+1) := by
    rw [pow_succ]; ring
  rw [hp] at he
  simpa only [correction, increment_power_jets n j F hF,
    coefficientField_nsmul, map_nsmul] using he

theorem power_step_actual (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) (r : ℕ) (G : Cylinder) :
    (((∑ k ∈ Finset.range (2*m), r.descFactorial k • productChannel m T k
        (coefficientField n m hm T hT j (F*(MvPolynomial.X j)^(r-k)))) (core G) : ℝ) : ℂ) =
      cylindricalExpectation m hm T hT (cylinderOf n (F*(MvPolynomial.X j)^(r+1))*G) := by
  have he := congrArg (fun φ : Dual => (φ (core G):ℂ))
    (power_step_dual n m hm T hT j F hF r)
  exact he.symm.trans (pairing_core_complex m hm T hT _ G)

end OperatorDerivativeRewrite.Foundation.HigherHeatAllPowerSteps
