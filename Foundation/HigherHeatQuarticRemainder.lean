import Foundation.HigherHeatQuarticStepIdentity

/-! Operator-norm decay of fourth-power signed-step corrections.
No positivity or signed second-moment estimate is used. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatQuarticRemainder
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatWeakStepFields HigherHeatDyadicStepAgreement
open HigherHeatSecondChannelSteps HigherHeatThirdChannelSteps HigherHeatFourthChannelSteps
open HigherHeatCubicRemainder HigherHeatCubicStepIdentity HigherHeatQuarticStepIdentity
open HigherHeatPairedDualCausality

theorem fourth_bound (T : ℝ≥0) (A : Field timeMeasure) :
    ‖fourthChannel T A‖ ≤ 24*(T:ℝ)*‖A‖ := by
  change ‖(6*coefficient 2 T) • transpose timeMeasure 0 A‖ ≤ _
  have hc : |6*coefficient 2 T| = 24*(T:ℝ) := by
    norm_num [coefficient, abs_mul, abs_of_nonneg T.coe_nonneg]; ring
  calc
    _ ≤ ‖6*coefficient 2 T‖ * ‖transpose timeMeasure 0 A‖ :=
      ContinuousLinearMap.opNorm_smul_le (𝕜 := ℝ) (𝕜₂ := ℝ) _ _
    _ = (24*(T:ℝ))*‖transpose timeMeasure 0 A‖ := by rw [Real.norm_eq_abs, hc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (transpose_bound timeMeasure 0 A) (by positivity)

theorem third_step_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) :
    ‖thirdChannel T (coefficientField n 2 (by norm_num) T hT j F)‖ ≤
      24*(T:ℝ)*(‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖ *
        (HigherHeatDyadicLaws.duration 1 n:ℝ)) := by
  simpa only [coefficientField, step_norm, gridCell_measure] using
    third_bound T (coefficientField n 2 (by norm_num) T hT j F)

theorem cubic_increment_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    ‖pairing 2 (by norm_num) T hT (core (cylinderOf n (F*(MvPolynomial.X j)^3)))‖ ≤
      (24*(T:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) +
        144*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2 +
        64*(T:ℝ)^3*(HigherHeatDyadicLaws.duration 1 n:ℝ)^3)*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖ := by
  rw [cubic_step_dual n T hT j F hF]
  change ‖HigherHeatCubicRemainder.cellRemainder n T hT j F +
    thirdChannel T (coefficientField n 2 (by norm_num) T hT j F)‖ ≤ _
  exact (norm_add_le _ _).trans
    ((add_le_add (HigherHeatCubicRemainder.cell_remainder_bound n T hT j F hF)
      (third_step_bound n T hT j F)).trans_eq (by ring))

theorem first_cubic_step_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    ‖firstChannel 2 T
      (coefficientField n 2 (by norm_num) T hT j (F*(MvPolynomial.X j)^3))‖ ≤
      (96*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2 +
        576*(T:ℝ)^3*(HigherHeatDyadicLaws.duration 1 n:ℝ)^3 +
        256*(T:ℝ)^4*(HigherHeatDyadicLaws.duration 1 n:ℝ)^4)*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖ := by
  have h := cubic_increment_bound n T hT j F hF
  calc
    _ ≤ _ := first_step_bound n T hT j (F*(MvPolynomial.X j)^3)
    _ ≤ 4*(T:ℝ)*(((24*(T:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) +
        144*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2 +
        64*(T:ℝ)^3*(HigherHeatDyadicLaws.duration 1 n:ℝ)^3)*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖)*
        (HigherHeatDyadicLaws.duration 1 n:ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h
        (HigherHeatDyadicLaws.duration 1 n).coe_nonneg) (by positivity)
    _ = _ := by ring

theorem second_quadratic_step_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    ‖secondChannel 2 T
      (coefficientField n 2 (by norm_num) T hT j (F*(MvPolynomial.X j)^2))‖ ≤
      (144*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2 +
        192*(T:ℝ)^3*(HigherHeatDyadicLaws.duration 1 n:ℝ)^3)*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖ := by
  have h := quadratic_increment_bound n T hT j F hF
  calc
    _ ≤ _ := second_step_bound n T hT j (F*(MvPolynomial.X j)^2)
    _ ≤ 12*(T:ℝ)*(((16*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2 +
        12*(T:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖)*
        (HigherHeatDyadicLaws.duration 1 n:ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h
        (HigherHeatDyadicLaws.duration 1 n).coe_nonneg) (by positivity)
    _ = _ := by ring

theorem third_linear_step_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    ‖thirdChannel T
      (coefficientField n 2 (by norm_num) T hT j (F*MvPolynomial.X j))‖ ≤
      (96*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2)*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖ := by
  have h := linear_increment_bound n T hT j F hF
  calc
    _ ≤ _ := third_step_bound n T hT j (F*MvPolynomial.X j)
    _ ≤ 24*(T:ℝ)*(((4*(T:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖)*
        (HigherHeatDyadicLaws.duration 1 n:ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h
        (HigherHeatDyadicLaws.duration 1 n).coe_nonneg) (by positivity)
    _ = _ := by ring

def cellRemainder (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) : Dual :=
  firstChannel 2 T (coefficientField n 2 (by norm_num) T hT j (F*(MvPolynomial.X j)^3)) +
    (3:ℕ) • secondChannel 2 T
      (coefficientField n 2 (by norm_num) T hT j (F*(MvPolynomial.X j)^2)) +
    (3:ℕ) • thirdChannel T (coefficientField n 2 (by norm_num) T hT j (F*MvPolynomial.X j))

theorem cell_remainder_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    ‖cellRemainder n T hT j F‖ ≤
      (816*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2 +
        1152*(T:ℝ)^3*(HigherHeatDyadicLaws.duration 1 n:ℝ)^3 +
        256*(T:ℝ)^4*(HigherHeatDyadicLaws.duration 1 n:ℝ)^4)*
        ‖pairing 2 (by norm_num) T hT (core (cylinderOf n F))‖ := by
  have ha := first_cubic_step_bound n T hT j F hF
  have hb := second_quadratic_step_bound n T hT j F hF
  have hc := third_linear_step_bound n T hT j F hF
  unfold cellRemainder
  calc
    _ ≤ (‖firstChannel 2 T
        (coefficientField n 2 (by norm_num) T hT j (F*(MvPolynomial.X j)^3))‖ +
      3*‖secondChannel 2 T
        (coefficientField n 2 (by norm_num) T hT j (F*(MvPolynomial.X j)^2))‖) +
      3*‖thirdChannel T
        (coefficientField n 2 (by norm_num) T hT j (F*MvPolynomial.X j))‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add
      · exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_nsmul_le))
      · exact norm_nsmul_le
    _ ≤ _ := add_le_add (add_le_add ha (mul_le_mul_of_nonneg_left hb (by norm_num)))
      (mul_le_mul_of_nonneg_left hc (by norm_num))
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.HigherHeatQuarticRemainder
