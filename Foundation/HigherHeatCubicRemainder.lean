import Foundation.HigherHeatCubicStepIdentity

/-! Dual-norm bounds for the actual cubic signed-step corrections. -/
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCubicRemainder
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatWeakTimeAdjoint HigherHeatWeakStepFields HigherHeatDyadicStepAgreement
open HigherHeatCompletedPairing HigherHeatSecondChannelSteps HigherHeatThirdChannelSteps
open HigherHeatPairedDualCausality HigherHeatCompletedStepAgreement HigherHeatCompletedAffineSteps

theorem second_bound (T : ℝ≥0) (A : Field timeMeasure) :
    ‖secondChannel 2 T A‖ ≤ 12*(T:ℝ)*‖A‖ := by
  change ‖(coefficient 2 T * (3:ℝ)) • transpose timeMeasure 2 A‖ ≤ _
  have hc : |coefficient 2 T * (3:ℝ)| = 12*(T:ℝ) := by
    norm_num [coefficient, abs_mul, abs_of_nonneg T.coe_nonneg]; ring
  calc
    _ ≤ ‖coefficient 2 T * (3:ℝ)‖ * ‖transpose timeMeasure 2 A‖ :=
      ContinuousLinearMap.opNorm_smul_le (𝕜 := ℝ) (𝕜₂ := ℝ) _ _
    _ = (12*(T:ℝ))*‖transpose timeMeasure 2 A‖ := by rw [Real.norm_eq_abs, hc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (transpose_bound timeMeasure 2 A) (by positivity)

theorem third_bound (T : ℝ≥0) (A : Field timeMeasure) :
    ‖thirdChannel T A‖ ≤ 24*(T:ℝ)*‖A‖ := by
  change ‖(6*coefficient 2 T) • transpose timeMeasure 1 A‖ ≤ _
  have hc : |6*coefficient 2 T| = 24*(T:ℝ) := by
    norm_num [coefficient, abs_mul, abs_of_nonneg T.coe_nonneg]; ring
  calc
    _ ≤ ‖6*coefficient 2 T‖ * ‖transpose timeMeasure 1 A‖ :=
      ContinuousLinearMap.opNorm_smul_le (𝕜 := ℝ) (𝕜₂ := ℝ) _ _
    _ = (24*(T:ℝ))*‖transpose timeMeasure 1 A‖ := by rw [Real.norm_eq_abs, hc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (transpose_bound timeMeasure 1 A) (by positivity)

theorem second_step_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) :
    ‖secondChannel 2 T (coefficientField n 2 (by norm_num) T hT j F)‖ ≤
      12*(T:ℝ)*(‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖ *
        (HigherHeatDyadicLaws.duration 1 n:ℝ)) := by
  simpa only [coefficientField, step_norm, gridCell_measure] using
    second_bound T (coefficientField n 2 (by norm_num) T hT j F)

theorem first_step_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) :
    ‖firstChannel 2 T (coefficientField n 2 (by norm_num) T hT j F)‖ ≤
      4*(T:ℝ)*(‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖ *
        (HigherHeatDyadicLaws.duration 1 n:ℝ)) := by
  have h := firstChannel_step_bound 2 T (gridCell n j) (gridCell_measurable n j)
    (gridCell_finite n j) (pairing 2 (by norm_num) T hT (core (cylinderOf n F)))
  rw [gridCell_measure] at h
  exact h

theorem linear_increment_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    ‖pairing 2 (by norm_num) T hT (core (cylinderOf n (F*MvPolynomial.X j)))‖ ≤
      (4*(T:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖ := by
  rw [← agreement_dual n 2 (by norm_num) T hT j F hF]
  have h := firstChannel_step_bound 2 T (gridCell n j) (gridCell_measurable n j)
    (gridCell_finite n j) (pairing 2 (by norm_num) T hT (core (cylinderOf n F)))
  rw [gridCell_measure] at h
  norm_num at h
  exact h.trans_eq (by ring)

theorem quadratic_increment_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    ‖pairing 2 (by norm_num) T hT (core (cylinderOf n (F*(MvPolynomial.X j)^2)))‖ ≤
      (16*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2 +
        12*(T:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖ := by
  rw [quadratic_step_dual n 2 (by norm_num) T hT j F hF]
  have h₁ := quadratic_remainder_bound n 2 (by norm_num) T hT j F hF
  have h₂ := second_step_bound n T hT j F
  norm_num at h₁
  exact (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

def cellRemainder (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) : Dual :=
  firstChannel 2 T (coefficientField n 2 (by norm_num) T hT j (F*(MvPolynomial.X j)^2)) +
    secondChannel 2 T (coefficientField n 2 (by norm_num) T hT j (F*MvPolynomial.X j)) +
    secondChannel 2 T (coefficientField n 2 (by norm_num) T hT j (F*MvPolynomial.X j))

theorem first_quadratic_step_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    ‖firstChannel 2 T
      (coefficientField n 2 (by norm_num) T hT j (F*(MvPolynomial.X j)^2))‖ ≤
      (64*(T:ℝ)^3*(HigherHeatDyadicLaws.duration 1 n:ℝ)^3 +
        48*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2)*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖ := by
  have hQ := quadratic_increment_bound n T hT j F hF
  have hA := first_step_bound n T hT j (F*(MvPolynomial.X j)^2)
  calc
    _ ≤ _ := hA
    _ ≤ 4*(T:ℝ)*(((16*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2+
        12*(T:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖)*
        (HigherHeatDyadicLaws.duration 1 n:ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQ
        (HigherHeatDyadicLaws.duration 1 n).coe_nonneg) (by positivity)
    _ = _ := by ring

theorem second_linear_step_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    ‖secondChannel 2 T
      (coefficientField n 2 (by norm_num) T hT j (F*MvPolynomial.X j))‖ ≤
      (48*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2)*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖ := by
  have hL := linear_increment_bound n T hT j F hF
  have hB := second_step_bound n T hT j (F*MvPolynomial.X j)
  calc
    _ ≤ _ := hB
    _ ≤ 12*(T:ℝ)*(((4*(T:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖)*
        (HigherHeatDyadicLaws.duration 1 n:ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL
        (HigherHeatDyadicLaws.duration 1 n).coe_nonneg) (by positivity)
    _ = _ := by ring

theorem cell_remainder_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    ‖cellRemainder n T hT j F‖ ≤
      (144*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2 +
        64*(T:ℝ)^3*(HigherHeatDyadicLaws.duration 1 n:ℝ)^3)*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖ := by
  have ha := first_quadratic_step_bound n T hT j F hF
  have hb := second_linear_step_bound n T hT j F hF
  unfold cellRemainder
  calc
    _ ≤ (‖firstChannel 2 T
        (coefficientField n 2 (by norm_num) T hT j (F*(MvPolynomial.X j)^2))‖ +
      ‖secondChannel 2 T
        (coefficientField n 2 (by norm_num) T hT j (F*MvPolynomial.X j))‖) +
      ‖secondChannel 2 T
        (coefficientField n 2 (by norm_num) T hT j (F*MvPolynomial.X j))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add ha hb) hb
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.HigherHeatCubicRemainder
