import Foundation.HigherHeatAffineStepCorrection

/-! The second complementary derivative channel and actual finite signed step corrections. -/
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSecondChannelSteps
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatWeakTimeAdjoint
open HigherHeatWeakStepFields HigherHeatDyadicStepAgreement HigherHeatCompletedPairing
open HigherHeatTimeDerivative HigherHeatAffineStepCorrection MultivariateFactorialDomain
open HigherHeatGridDoubling HigherHeatStepRefinement

def secondChannel (m : ℕ) (T : ℝ≥0) : Field timeMeasure →L[ℝ] HigherHeatPairedDualCausality.Dual :=
  (coefficient m T * ((2*m-1:ℕ):ℝ)) • transpose timeMeasure (2*m-2)

theorem secondChannel_coefficientField (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F G : Test n) :
    secondChannel m T (coefficientField n m hm T hT j F) (core (cylinderOf n G)) =
      coefficient m T * ((2*m-1:ℕ):ℝ) * (HigherHeatDyadicLaws.duration 1 n:ℝ) *
        pairing m hm T hT (core (cylinderOf n F))
          (core (cylinderOf n ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[2*m-2] G))) := by
  change (coefficient m T * ((2*m-1:ℕ):ℝ)) * transpose timeMeasure (2*m-2)
    (step _ _ _ _ _) (core (cylinderOf n G)) = _
  rw [transpose_step_constant timeMeasure (2*m-2) (gridCell n j)
    (gridCell_measurable n j) (gridCell_finite n j) _ _ _
    ((MeasureTheory.ae_restrict_mem (gridCell_measurable n j)).mono (fun t ht =>
      derivative_core_on_cell n j t ht (2*m-2) G)), gridCell_measure]
  ring

theorem native_affine_agreement (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F G : Test n)
    (hF : polynomialDerivative (Pi.single j 1) (polynomialDerivative (Pi.single j 1) F) = 0) :
    pairing m hm T hT (core (cylinderOf n (F * MvPolynomial.X j))) (core (cylinderOf n G)) =
      firstChannel m T (coefficientField n m hm T hT j F) (core (cylinderOf n G)) +
        secondChannel m T (coefficientField n m hm T hT j
          (polynomialDerivative (Pi.single j 1) F)) (core (cylinderOf n G)) := by
  have hp (A B : Test n) :
      pairing m hm T hT (core (cylinderOf n A)) (core (cylinderOf n B)) =
        (HigherHeatMultivariateMoments.mean m hm
          (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n)
          (fun _ => HigherHeatDyadicLaws.duration_pos T hT n) (A*B)).re := by
    rw [pairing_core_real, ← map_mul (cylinderOf n), cylindricalExpectation_apply]
    rfl
  rw [coefficientField_integral, secondChannel_coefficientField, hp, hp, hp,
    actual_affine_stein _ _ _ _ j F G hF]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re, PureOrderPolynomialConditioning.parameters, coefficient]
  rw [← duration_scale T n]
  ring

theorem derivative_step (n : ℕ) (j : Fin (size n)) (k : Fin (size (n+1)))
    (hk : pairBlock k = j) (F : Test n) :
    polynomialDerivative (Pi.single k 1) (HigherHeatPolynomialCylinders.step n F) =
      HigherHeatPolynomialCylinders.step n (polynomialDerivative (Pi.single j 1) F) := by
  have he := derivative_pullback (@pairBlock (size n)) k F
  rw [hk] at he
  exact he

theorem affine_step (n : ℕ) (j : Fin (size n)) (k : Fin (size (n+1)))
    (hk : pairBlock k = j) (F : Test n)
    (hF : polynomialDerivative (Pi.single j 1) (polynomialDerivative (Pi.single j 1) F) = 0) :
    polynomialDerivative (Pi.single k 1) (polynomialDerivative (Pi.single k 1)
      (HigherHeatPolynomialCylinders.step n F)) = 0 := by
  rw [derivative_step n j k hk F, derivative_step n j k hk, hF, map_zero]

end OperatorDerivativeRewrite.Foundation.HigherHeatSecondChannelSteps
