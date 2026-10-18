import Foundation.HigherHeatQuadraticIto

/-! A rigorous boundary of the verified two-channel formula: higher-order centered powers
need additional channels. This does not refute a full multichannel Itô formula. -/
noncomputable section
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticItoBoundary
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatSecondChannelSteps HigherHeatFirstChannelRange
open HigherHeatTimeDerivative HigherHeatPairedDualCausality HigherHeatCompletedSignedMean

theorem secondChannel_terminal_zero (m : ℕ) (hm : 1 < m) (T : ℝ≥0)
    (A : Field timeMeasure) : secondChannel m T A (core terminalCylinder) = 0 := by
  change (coefficient m T * ((2*m-1:ℕ):ℝ)) *
    transpose timeMeasure (2*m-2) A (core terminalCylinder) = 0
  rw [transpose_apply]
  have hz (t : ℝ) : ((atTime t)^(2*m-2)) (core terminalCylinder) = 0 := by
    rw [← terminal_coordinate]
    exact atTime_pow_coordinate_zero t 0 (HigherHeatTerminalPositions.lastIndex 0) (2*m-2) (by omega)
  simp only [hz, map_zero, MeasureTheory.integral_zero, mul_zero]

theorem no_twoChannel_representation (m : ℕ) (hm : 1 < m) (T : ℝ≥0) (hT : 0 < T)
    (A B : Field timeMeasure) :
    firstChannel m T A + secondChannel m T B ≠
      pairing m (by omega) T hT (core (terminalCylinder^(2*m-1))) := by
  intro he
  have hh := congrArg (fun φ : Dual => φ (core terminalCylinder)) he
  change firstChannel m T A (core terminalCylinder) + secondChannel m T B (core terminalCylinder) = _ at hh
  rw [firstChannel_terminal_zero m hm, secondChannel_terminal_zero m hm, zero_add, witness_pairing] at hh
  have hn : ((2*m).factorial:ℝ)*((-1:ℝ)^(m+1)*(T:ℝ)) ≠ 0 :=
    mul_ne_zero (by positivity)
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (by exact_mod_cast hT)))
  exact hn hh.symm

theorem higher_quadratic_centered (m : ℕ) (hm : 1 < m) (T : ℝ≥0) (hT : 0 < T) :
    mean m (by omega) T hT (core (terminalCylinder^2)) = 0 := by
  rw [mean_core_real, terminal_moments]
  have hd : ¬ 2*m ∣ 2 := by
    intro h
    have hh := Nat.le_of_dvd (by norm_num : 0 < (2:ℕ)) h
    omega
  rw [PseudoPolynomialStein.moment_off_order (2*m) (by omega) _ _ hd]
  rfl

theorem biharmonic_cubic_obstruction (T : ℝ≥0) (hT : 0 < T) :
    mean 2 (by norm_num) T hT (core (terminalCylinder^3)) = 0 ∧
    Polynomial.derivative^[4] ((Polynomial.X : Polynomial ℝ)^3) = 0 ∧
    ∀ A B : Field timeMeasure, firstChannel 2 T A + secondChannel 2 T B ≠
      pairing 2 (by norm_num) T hT (core (terminalCylinder^3)) := by
  refine ⟨witness_centered 2 (by norm_num) T hT, ?_, ?_⟩
  · rw [Polynomial.iterate_derivative_X_pow_eq_smul,
      Nat.descFactorial_eq_zero_iff_lt.mpr (by norm_num : 3 < 4), Nat.cast_zero, zero_smul]
  · exact fun A B => no_twoChannel_representation 2 (by norm_num) T hT A B

end OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticItoBoundary
