import Foundation.HigherHeatCompletedAffineSteps

/-! The third biharmonic channel. Quadratic coefficient identities below are
actual finite signed-kernel pairings, including tests on arbitrary finer grids.
No full chronological reconstruction is assumed. -/
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatThirdChannelSteps
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatWeakTimeAdjoint HigherHeatWeakStepFields HigherHeatDyadicStepAgreement
open HigherHeatCompletedPairing HigherHeatSecondChannelSteps HigherHeatAffineStepCorrection
open HigherHeatGridDoubling HigherHeatStepRefinement MultivariateFactorialDomain
open HigherHeatPairedDualCausality HigherHeatTimeDerivative

def thirdChannel (T : ℝ≥0) : Field timeMeasure →L[ℝ] Dual :=
  (6 * coefficient 2 T) • transpose timeMeasure 1

theorem derivative_three_mul {ι : Type*} (v : ι → ℝ) (F G : MvPolynomial ι ℝ)
    (hF : (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[3] F = 0) :
    (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[3] (F*G) =
      F * (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[3] G +
      (3:ℝ) • (polynomialDerivative v F * polynomialDerivative v (polynomialDerivative v G)) +
      (3:ℝ) • (polynomialDerivative v (polynomialDerivative v F) * polynomialDerivative v G) := by
  let D := polynomialDerivative v
  have hp (A B : MvPolynomial ι ℝ) : D (A*B) = A*D B+B*D A := by
    simpa only [smul_eq_mul] using Derivation.leibniz D A B
  change D (D (D F)) = 0 at hF
  change D (D (D (F*G))) = F*D (D (D G)) +
    (3:ℝ) • (D F*D (D G)) + (3:ℝ) • (D (D F)*D G)
  have hc : (MvPolynomial.C (3:ℝ) : MvPolynomial ι ℝ) = 3 := by
    calc
      _ = MvPolynomial.C ((1:ℝ)+1+1) := congrArg _ (by norm_num)
      _ = 3 := by rw [MvPolynomial.C_add, MvPolynomial.C_add, MvPolynomial.C_1]; ring
  simp only [hp, map_add, hF, MvPolynomial.smul_eq_C_mul]
  rw [hc]
  ring

theorem thirdChannel_coefficientField (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F G : Test n) :
    thirdChannel T (coefficientField n 2 (by norm_num) T hT j F) (core (cylinderOf n G)) =
      6 * coefficient 2 T * (HigherHeatDyadicLaws.duration 1 n:ℝ) *
        pairing 2 (by norm_num) T hT (core (cylinderOf n F))
          (core (cylinderOf n (polynomialDerivative (Pi.single j 1) G))) := by
  change (6 * coefficient 2 T) * transpose timeMeasure 1
    (step _ _ _ _ _) (core (cylinderOf n G)) = _
  rw [transpose_step_constant timeMeasure 1 (gridCell n j)
    (gridCell_measurable n j) (gridCell_finite n j) _ _ _
    ((MeasureTheory.ae_restrict_mem (gridCell_measurable n j)).mono (fun t ht =>
      derivative_core_on_cell n j t ht 1 G)), gridCell_measure]
  simp only [Function.iterate_one]
  ring

theorem native_quadratic_agreement (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F G : Test n)
    (hF : (polynomialDerivative (Pi.single j 1) : Test n → Test n)^[3] F = 0) :
    pairing 2 (by norm_num) T hT (core (cylinderOf n (F * MvPolynomial.X j)))
        (core (cylinderOf n G)) =
      firstChannel 2 T (coefficientField n 2 (by norm_num) T hT j F) (core (cylinderOf n G)) +
      secondChannel 2 T (coefficientField n 2 (by norm_num) T hT j
        (polynomialDerivative (Pi.single j 1) F)) (core (cylinderOf n G)) +
      (1/2:ℝ) * thirdChannel T (coefficientField n 2 (by norm_num) T hT j
        (polynomialDerivative (Pi.single j 1) (polynomialDerivative (Pi.single j 1) F)))
          (core (cylinderOf n G)) := by
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
  rw [show 2*2-1=3 by norm_num, derivative_three_mul _ F G hF,
    map_add, map_add, map_smul, map_smul] at hs
  rw [coefficientField_integral, secondChannel_coefficientField, thirdChannel_coefficientField,
    hp, hp, hp, hp]
  have hleft : (F * MvPolynomial.X j) * G = MvPolynomial.X j * (F*G) := by ring
  rw [hleft, hs]
  simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, PureOrderPolynomialConditioning.parameters, coefficient]
  rw [← HigherHeatDyadicStepAgreement.duration_scale T n]
  norm_num
  ring

theorem derivative_iterate_step (n : ℕ) (j : Fin (size n)) (k : Fin (size (n + 1)))
    (hk : pairBlock k = j) (F : Test n) (r : ℕ) :
    (polynomialDerivative (Pi.single k 1) : Test (n+1) → Test (n+1))^[r]
        (HigherHeatPolynomialCylinders.step n F) =
      HigherHeatPolynomialCylinders.step n
        ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[r] F) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, derivative_step n j k hk,
      Function.iterate_succ_apply']

def quadraticCorrection (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) : Dual :=
  firstChannel 2 T (coefficientField n 2 (by norm_num) T hT j F) +
    secondChannel 2 T (coefficientField n 2 (by norm_num) T hT j
      (polynomialDerivative (Pi.single j 1) F)) +
    (1/2:ℝ) • thirdChannel T (coefficientField n 2 (by norm_num) T hT j
      (polynomialDerivative (Pi.single j 1) (polynomialDerivative (Pi.single j 1) F)))

theorem quadraticCorrection_split (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) :
    quadraticCorrection n T hT j F =
      quadraticCorrection (n+1) T hT (evenIndex j) (HigherHeatPolynomialCylinders.step n F) +
      quadraticCorrection (n+1) T hT (oddIndex j) (HigherHeatPolynomialCylinders.step n F) := by
  have hl : pairBlock (evenIndex j) = j := by apply Fin.ext; simp [pairBlock, evenIndex]
  have hr : pairBlock (oddIndex j) = j := by apply Fin.ext; dsimp [pairBlock, oddIndex]; omega
  have hdl := derivative_step n j (evenIndex j) hl F
  have hdr := derivative_step n j (oddIndex j) hr F
  have hddl := derivative_step n j (evenIndex j) hl (polynomialDerivative (Pi.single j 1) F)
  have hddr := derivative_step n j (oddIndex j) hr (polynomialDerivative (Pi.single j 1) F)
  simp only [quadraticCorrection, hdl, hdr, hddl, hddr]
  rw [coefficientField_split n 2 (by norm_num) T hT j F,
    coefficientField_split n 2 (by norm_num) T hT j (polynomialDerivative (Pi.single j 1) F),
    coefficientField_split n 2 (by norm_num) T hT j
      (polynomialDerivative (Pi.single j 1) (polynomialDerivative (Pi.single j 1) F))]
  simp only [map_add, smul_add]
  abel

theorem quadratic_agreement_finer (d n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n)
    (hF : (polynomialDerivative (Pi.single j 1) : Test n → Test n)^[3] F = 0)
    (G : Test (n + d)) :
    pairing 2 (by norm_num) T hT (core (cylinderOf n (F * MvPolynomial.X j)))
        (core (cylinderOf (n+d) G)) =
      quadraticCorrection n T hT j F (core (cylinderOf (n+d) G)) := by
  induction d generalizing n with
  | zero => exact native_quadratic_agreement n T hT j F G hF
  | succ d ih =>
    have he : n+(d+1) = (n+1)+d := by omega
    revert G
    rw [he]
    intro G
    have hl : pairBlock (evenIndex j) = j := by apply Fin.ext; simp [pairBlock, evenIndex]
    have hr : pairBlock (oddIndex j) = j := by apply Fin.ext; dsimp [pairBlock, oddIndex]; omega
    have hL := ih (n+1) (evenIndex j) (HigherHeatPolynomialCylinders.step n F)
      (by rw [derivative_iterate_step n j _ hl F 3, hF, map_zero]) G
    have hR := ih (n+1) (oddIndex j) (HigherHeatPolynomialCylinders.step n F)
      (by rw [derivative_iterate_step n j _ hr F 3, hF, map_zero]) G
    rw [stochastic_polynomial_split n j F, quadraticCorrection_split]
    simp only [map_add, add_apply]
    exact congrArg₂ (fun a b : ℝ => a+b) hL hR

theorem quadratic_agreement_dual (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n)
    (hF : (polynomialDerivative (Pi.single j 1) : Test n → Test n)^[3] F = 0) :
    pairing 2 (by norm_num) T hT (core (cylinderOf n (F * MvPolynomial.X j))) =
      firstChannel 2 T (coefficientField n 2 (by norm_num) T hT j F) +
      secondChannel 2 T (coefficientField n 2 (by norm_num) T hT j
        (polynomialDerivative (Pi.single j 1) F)) +
      (1/2:ℝ) • thirdChannel T (coefficientField n 2 (by norm_num) T hT j
        (polynomialDerivative (Pi.single j 1) (polynomialDerivative (Pi.single j 1) F))) := by
  apply ContinuousLinearMap.coeFn_injective
  apply core_dense.equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext G
  change _ = firstChannel 2 T (coefficientField n 2 (by norm_num) T hT j F) (core G) +
    secondChannel 2 T (coefficientField n 2 (by norm_num) T hT j
      (polynomialDerivative (Pi.single j 1) F)) (core G) +
    (1/2:ℝ) * thirdChannel T (coefficientField n 2 (by norm_num) T hT j
      (polynomialDerivative (Pi.single j 1) (polynomialDerivative (Pi.single j 1) F))) (core G)
  apply HigherHeatCylindricalConditioning.tail_induction n (fun G =>
    pairing 2 (by norm_num) T hT (core (cylinderOf n (F * MvPolynomial.X j))) (core G) =
      firstChannel 2 T (coefficientField n 2 (by norm_num) T hT j F) (core G) +
      secondChannel 2 T (coefficientField n 2 (by norm_num) T hT j
        (polynomialDerivative (Pi.single j 1) F)) (core G) +
      (1/2:ℝ) * thirdChannel T (coefficientField n 2 (by norm_num) T hT j
        (polynomialDerivative (Pi.single j 1) (polynomialDerivative (Pi.single j 1) F)))
          (core G)) _ G
  intro N hn P
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact quadratic_agreement_finer d n T hT j F hF P

end OperatorDerivativeRewrite.Foundation.HigherHeatThirdChannelSteps
