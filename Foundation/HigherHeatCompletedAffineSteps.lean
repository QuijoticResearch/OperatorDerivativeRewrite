import Foundation.HigherHeatSecondChannelSteps

/-! Completed signed affine-product identities and the quadratic-channel remainder estimate. -/
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCompletedAffineSteps
open HigherHeatPolynomialCylinders HigherHeatGridDoubling HigherHeatDyadicStepAgreement
open HigherHeatStepRefinement HigherHeatWeakTimeAdjoint HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatSecondChannelSteps HigherHeatWeakStepFields
open MultivariateFactorialDomain MultivariateFactorialSubstitution HigherHeatPairedDualCausality

theorem affine_agreement_finer (d : ℕ) (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n)
    (hF : polynomialDerivative (Pi.single j 1) (polynomialDerivative (Pi.single j 1) F) = 0)
    (G : Test (n+d)) :
    pairing m hm T hT (core (cylinderOf n (F * MvPolynomial.X j))) (core (cylinderOf (n+d) G)) =
      firstChannel m T (coefficientField n m hm T hT j F) (core (cylinderOf (n+d) G)) +
        secondChannel m T (coefficientField n m hm T hT j
          (polynomialDerivative (Pi.single j 1) F)) (core (cylinderOf (n+d) G)) := by
  induction d generalizing n with
  | zero => exact native_affine_agreement n m hm T hT j F G hF
  | succ d ih =>
    have he : n+(d+1) = (n+1)+d := by omega
    revert G
    rw [he]
    intro G
    have hl : pairBlock (evenIndex j) = j := by apply Fin.ext; simp [pairBlock, evenIndex]
    have hr : pairBlock (oddIndex j) = j := by apply Fin.ext; dsimp [pairBlock, oddIndex]; omega
    rw [stochastic_polynomial_split n j F, coefficientField_split n m hm T hT j F,
      coefficientField_split n m hm T hT j (polynomialDerivative (Pi.single j 1) F)]
    simp only [map_add, add_apply]
    have hL := ih (n+1) (evenIndex j) (HigherHeatPolynomialCylinders.step n F)
      (affine_step n j _ hl F hF) G
    have hR := ih (n+1) (oddIndex j) (HigherHeatPolynomialCylinders.step n F)
      (affine_step n j _ hr F hF) G
    rw [derivative_step n j _ hl F] at hL
    rw [derivative_step n j _ hr F] at hR
    exact (congrArg₂ (fun a b : ℝ => a+b) hL hR).trans (add_add_add_comm _ _ _ _)

theorem affine_agreement_dual (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n)
    (hF : polynomialDerivative (Pi.single j 1) (polynomialDerivative (Pi.single j 1) F) = 0) :
    pairing m hm T hT (core (cylinderOf n (F * MvPolynomial.X j))) =
      firstChannel m T (coefficientField n m hm T hT j F) +
        secondChannel m T (coefficientField n m hm T hT j
          (polynomialDerivative (Pi.single j 1) F)) := by
  apply ContinuousLinearMap.coeFn_injective
  apply core_dense.equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext G
  change _ = firstChannel m T (coefficientField n m hm T hT j F) (core G) +
    secondChannel m T (coefficientField n m hm T hT j
      (polynomialDerivative (Pi.single j 1) F)) (core G)
  apply HigherHeatCylindricalConditioning.tail_induction n (fun G =>
    pairing m hm T hT (core (cylinderOf n (F * MvPolynomial.X j))) (core G) =
      firstChannel m T (coefficientField n m hm T hT j F) (core G) +
        secondChannel m T (coefficientField n m hm T hT j
          (polynomialDerivative (Pi.single j 1) F)) (core G)) _ G
  intro N hn P
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact affine_agreement_finer d n m hm T hT j F hF P

theorem quadratic_step_dual (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    pairing m hm T hT (core (cylinderOf n (F * (MvPolynomial.X j)^2))) =
      firstChannel m T (coefficientField n m hm T hT j (F * MvPolynomial.X j)) +
        secondChannel m T (coefficientField n m hm T hT j F) := by
  have hD := HigherHeatAdaptedStepDuality.derivative_zero_of_missing j F hF
  have hx : polynomialDerivative (Pi.single j 1) (F * MvPolynomial.X j) = F := by
    rw [Derivation.leibniz, hD, polynomialDerivative_X]
    simp only [Pi.single_eq_same, MvPolynomial.C_1, smul_eq_mul, mul_one, mul_zero, add_zero]
  have hD2 : polynomialDerivative (Pi.single j 1)
      (polynomialDerivative (Pi.single j 1) (F * MvPolynomial.X j)) = 0 := by rw [hx, hD]
  have he := affine_agreement_dual n m hm T hT j (F * MvPolynomial.X j) hD2
  rw [hx, mul_assoc, ← pow_two] at he
  exact he

theorem quadratic_remainder_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    ‖firstChannel m T (coefficientField n m hm T hT j (F * MvPolynomial.X j))‖ ≤
      ((((2*m:ℕ):ℝ)*(T:ℝ))*(HigherHeatDyadicLaws.duration 1 n:ℝ))^2 *
        ‖pairing m hm T hT (core (cylinderOf n F))‖ := by
  have h₂ : ‖pairing m hm T hT (core (cylinderOf n (F * MvPolynomial.X j)))‖ ≤
      ((2*m:ℕ):ℝ)*(T:ℝ) *
        (‖pairing m hm T hT (core (cylinderOf n F))‖ * (HigherHeatDyadicLaws.duration 1 n:ℝ)) := by
    rw [← HigherHeatCompletedStepAgreement.agreement_dual n m hm T hT j F hF]
    exact firstChannel_step_bound m T (gridCell n j) (gridCell_measurable n j)
      (gridCell_finite n j) _ |>.trans_eq (by rw [gridCell_measure])
  have h₁ := firstChannel_step_bound m T (gridCell n j) (gridCell_measurable n j)
    (gridCell_finite n j) (pairing m hm T hT (core (cylinderOf n (F * MvPolynomial.X j))))
  rw [gridCell_measure] at h₁
  calc
    _ ≤ _ := h₁
    _ ≤ ((2*m:ℕ):ℝ)*(T:ℝ) *
        ((((2*m:ℕ):ℝ)*(T:ℝ) *
          (‖pairing m hm T hT (core (cylinderOf n F))‖ * (HigherHeatDyadicLaws.duration 1 n:ℝ))) *
          (HigherHeatDyadicLaws.duration 1 n:ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right h₂ (HigherHeatDyadicLaws.duration 1 n).coe_nonneg) (by positivity)
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.HigherHeatCompletedAffineSteps
