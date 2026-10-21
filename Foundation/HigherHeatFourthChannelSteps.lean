import Foundation.HigherHeatThirdChannelSteps

/-! The bounded fourth (drift) channel and unrestricted polynomial signed-step
identity. Equality holds on the completed analytic test dual after refinement. -/
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourthChannelSteps
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatWeakTimeAdjoint HigherHeatWeakStepFields HigherHeatDyadicStepAgreement
open HigherHeatCompletedPairing HigherHeatSecondChannelSteps HigherHeatThirdChannelSteps
open HigherHeatGridDoubling HigherHeatStepRefinement MultivariateFactorialDomain
open HigherHeatPairedDualCausality HigherHeatTimeDerivative

def fourthChannel (T : ℝ≥0) : Field timeMeasure →L[ℝ] Dual :=
  (6 * coefficient 2 T) • transpose timeMeasure 0

theorem derivative_three_mul_full {ι : Type*} (v : ι → ℝ) (F G : MvPolynomial ι ℝ) :
    (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[3] (F*G) =
      F * (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[3] G +
      (3:ℝ) • (polynomialDerivative v F * polynomialDerivative v (polynomialDerivative v G)) +
      (3:ℝ) • (polynomialDerivative v (polynomialDerivative v F) * polynomialDerivative v G) +
      (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[3] F * G := by
  let D := polynomialDerivative v
  have hp (A B : MvPolynomial ι ℝ) : D (A*B) = A*D B+B*D A := by
    simpa only [smul_eq_mul] using Derivation.leibniz D A B
  change D (D (D (F*G))) = F*D (D (D G)) +
    (3:ℝ) • (D F*D (D G)) + (3:ℝ) • (D (D F)*D G) + D (D (D F))*G
  have hc : (MvPolynomial.C (3:ℝ) : MvPolynomial ι ℝ) = 3 := by
    calc
      _ = MvPolynomial.C ((1:ℝ)+1+1) := congrArg _ (by norm_num)
      _ = 3 := by rw [MvPolynomial.C_add, MvPolynomial.C_add, MvPolynomial.C_1]; ring
  simp only [hp, map_add, MvPolynomial.smul_eq_C_mul]
  rw [hc]
  ring

theorem fourthChannel_coefficientField (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F G : Test n) :
    fourthChannel T (coefficientField n 2 (by norm_num) T hT j F) (core (cylinderOf n G)) =
      6 * coefficient 2 T * (HigherHeatDyadicLaws.duration 1 n:ℝ) *
        pairing 2 (by norm_num) T hT (core (cylinderOf n F)) (core (cylinderOf n G)) := by
  change (6 * coefficient 2 T) * transpose timeMeasure 0
    (step _ _ _ _ _) (core (cylinderOf n G)) = _
  rw [transpose_step_constant timeMeasure 0 (gridCell n j)
    (gridCell_measurable n j) (gridCell_finite n j) _ _ _
    ((MeasureTheory.ae_restrict_mem (gridCell_measurable n j)).mono (fun t ht =>
      derivative_core_on_cell n j t ht 0 G)), gridCell_measure]
  simp only [Function.iterate_zero, id_eq]
  ring

def correction (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (j : Fin (size n)) (F : Test n) : Dual :=
  quadraticCorrection n T hT j F +
    (1/6:ℝ) • fourthChannel T (coefficientField n 2 (by norm_num) T hT j
      ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[3] F))

theorem native_agreement (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F G : Test n) :
    pairing 2 (by norm_num) T hT (core (cylinderOf n (F * MvPolynomial.X j)))
      (core (cylinderOf n G)) = correction n T hT j F (core (cylinderOf n G)) := by
  have hp (A B : Test n) :
      pairing 2 (by norm_num) T hT (core (cylinderOf n A)) (core (cylinderOf n B)) =
        (HigherHeatMultivariateMoments.mean 2 (by norm_num)
          (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n)
          (fun _ => HigherHeatDyadicLaws.duration_pos T hT n) (A*B)).re := by
    rw [pairing_core_real, ← map_mul (cylinderOf n), cylindricalExpectation_apply]
    rfl
  have hs := MultivariateConditionalStein.actual_coordinate_stein 2 (by norm_num)
    (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n)
    (fun _ => HigherHeatDyadicLaws.duration_pos T hT n) j (F*G)
  rw [show 2*2-1=3 by norm_num, derivative_three_mul_full,
    map_add, map_add, map_add, map_smul, map_smul] at hs
  simp only [correction, quadraticCorrection, add_apply,
    smul_apply, smul_eq_mul]
  rw [coefficientField_integral, secondChannel_coefficientField,
    thirdChannel_coefficientField, fourthChannel_coefficientField, hp, hp, hp, hp, hp]
  have hleft : (F * MvPolynomial.X j) * G = MvPolynomial.X j * (F*G) := by ring
  rw [hleft, hs]
  simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, PureOrderPolynomialConditioning.parameters, coefficient]
  rw [← HigherHeatDyadicStepAgreement.duration_scale T n]
  norm_num
  ring

theorem correction_split (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) :
    correction n T hT j F =
      correction (n+1) T hT (evenIndex j) (HigherHeatPolynomialCylinders.step n F) +
      correction (n+1) T hT (oddIndex j) (HigherHeatPolynomialCylinders.step n F) := by
  have hl : pairBlock (evenIndex j) = j := by apply Fin.ext; simp [pairBlock, evenIndex]
  have hr : pairBlock (oddIndex j) = j := by apply Fin.ext; dsimp [pairBlock, oddIndex]; omega
  simp only [correction, derivative_iterate_step n j _ hl F 3,
    derivative_iterate_step n j _ hr F 3]
  rw [quadraticCorrection_split,
    coefficientField_split n 2 (by norm_num) T hT j
      ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[3] F)]
  simp only [map_add, smul_add]
  abel

theorem agreement_finer (d n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (G : Test (n + d)) :
    pairing 2 (by norm_num) T hT (core (cylinderOf n (F * MvPolynomial.X j)))
      (core (cylinderOf (n + d) G)) = correction n T hT j F (core (cylinderOf (n + d) G)) := by
  induction d generalizing n with
  | zero => exact native_agreement n T hT j F G
  | succ d ih =>
    have he : n+(d+1) = (n+1)+d := by omega
    revert G
    rw [he]
    intro G
    have hL := ih (n+1) (evenIndex j) (HigherHeatPolynomialCylinders.step n F) G
    have hR := ih (n+1) (oddIndex j) (HigherHeatPolynomialCylinders.step n F) G
    rw [stochastic_polynomial_split n j F, correction_split]
    simp only [map_add, add_apply]
    exact congrArg₂ (fun a b : ℝ => a+b) hL hR

theorem agreement_dual (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) :
    pairing 2 (by norm_num) T hT (core (cylinderOf n (F * MvPolynomial.X j))) =
      correction n T hT j F := by
  apply ContinuousLinearMap.coeFn_injective
  apply core_dense.equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext G
  apply HigherHeatCylindricalConditioning.tail_induction n (fun G =>
    pairing 2 (by norm_num) T hT (core (cylinderOf n (F * MvPolynomial.X j))) (core G) =
      correction n T hT j F (core G)) _ G
  intro N hn P
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact agreement_finer d n T hT j F P

end OperatorDerivativeRewrite.Foundation.HigherHeatFourthChannelSteps
