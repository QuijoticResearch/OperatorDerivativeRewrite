import Foundation.HigherHeatQuadraticItoApproximation

/-! A concrete two-channel quadratic Itô identity for actual signed higher-heat sums,
with genuinely convergent predictable coefficient fields and completed test duality. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticIto
open MeasureTheory Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatPairedDualCausality HigherHeatWeakTimeAdjoint
open HigherHeatQuadraticItoData HigherHeatQuadraticItoFields HigherHeatQuadraticItoApproximation
open HigherHeatQuadraticChannelLimit HigherHeatSecondChannelSteps HigherHeatDyadicStepAgreement

theorem native_identity (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    pairing m hm T hT (core (terminalCylinder^2)) =
      firstChannel m T (adaptedField n m hm T hT (past n)) +
      firstChannel m T (adaptedField n m hm T hT (past n)) +
      pairing m hm T hT (core (cylinderOf n (quadraticPolynomial n (fun _ => 1)))) := by
  have hc : terminalCylinder^2 = cylinderOf n ((HigherHeatMultivariateMoments.terminal : Test n)^2) := by
    rw [HigherHeatTerminalPositions.terminal_on_grid n, map_pow]
  have hs := HigherHeatCompletedStepAgreement.adapted_sum_dual n m hm T hT (past n) (past_adapted n)
  rw [hc, quadratic_telescope]
  simp only [map_add, ← hs]

theorem linear_reconstruction (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    HigherHeatAdaptedIntegralClosure.integral m hm T hT (constantInput m hm T hT) =
      pairing m hm T hT (core terminalCylinder) := by
  change firstChannel m T (constantField m hm T hT) = _
  have he := HigherHeatCompletedStepAgreement.adapted_sum_dual 0 m hm T hT
    (fun _ => (1:Test 0)) (constants_adapted 0)
  rw [constants_field_eq] at he
  simpa only [HigherHeatAdaptedStepDuality.stepPolynomial, one_mul,
    terminalCylinder, HigherHeatMultivariateMoments.terminal] using he

theorem linear_steps_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => firstChannel m T (adaptedField n m hm T hT (past n))) atTop
      (𝓝 (HigherHeatAdaptedIntegralClosure.integral m hm T hT (curveInput m hm T hT))) := by
  change Tendsto (fun n => firstChannel m T (adaptedField n m hm T hT (past n))) atTop
    (𝓝 (firstChannel m T (curveField m hm T hT)))
  exact ((firstChannel m T).continuous.tendsto (curveField m hm T hT)).comp (past_fields_tendsto m hm T hT)

theorem quadratic_steps_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => pairing m hm T hT (core (cylinderOf n (quadraticPolynomial n (fun _ => 1)))))
      atTop (𝓝 (secondChannel m T (constantInput m hm T hT).val)) := by
  have hc : Tendsto (fun n => adaptedField n m hm T hT (fun _ => (1:Test n)))
      atTop (𝓝 (constantInput m hm T hT).val) := by
    change Tendsto (fun n => adaptedField n m hm T hT (fun _ => (1:Test n)))
      atTop (𝓝 (constantField m hm T hT))
    simpa only [constants_field_eq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => constantField m hm T hT) atTop (𝓝 (constantField m hm T hT)))
  have hM (n : ℕ) (j : Fin (size n)) :
      ‖pairing m hm T hT (core (cylinderOf n (1:Test n)))‖ ≤
        ‖pairing m hm T hT (core (1:Cylinder))‖ := by rw [map_one]
  exact quadratic_sums_converge m hm T hT (fun _ _ => 1) constants_adapted
    ‖pairing m hm T hT (core (1:Cylinder))‖ hM (constantInput m hm T hT) hc

theorem quadratic_ito (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    pairing m hm T hT (core (terminalCylinder^2)) =
      HigherHeatAdaptedIntegralClosure.integral m hm T hT (curveInput m hm T hT) +
      HigherHeatAdaptedIntegralClosure.integral m hm T hT (curveInput m hm T hT) +
      secondChannel m T (constantInput m hm T hT).val := by
  letI : ContinuousAdd Dual := (inferInstance : IsTopologicalAddGroup Dual).toContinuousAdd
  have hsum : Tendsto (fun n => firstChannel m T (adaptedField n m hm T hT (past n)) +
      firstChannel m T (adaptedField n m hm T hT (past n)) +
      pairing m hm T hT (core (cylinderOf n (quadraticPolynomial n (fun _ => 1)))))
    atTop (𝓝 (HigherHeatAdaptedIntegralClosure.integral m hm T hT (curveInput m hm T hT) +
      HigherHeatAdaptedIntegralClosure.integral m hm T hT (curveInput m hm T hT) +
      secondChannel m T (constantInput m hm T hT).val)) :=
    ((linear_steps_tendsto m hm T hT).add (linear_steps_tendsto m hm T hT)).add
      (quadratic_steps_tendsto m hm T hT)
  have hconst : Tendsto (fun _ : ℕ => pairing m hm T hT (core (terminalCylinder^2)))
      atTop (𝓝 (HigherHeatAdaptedIntegralClosure.integral m hm T hT (curveInput m hm T hT) +
        HigherHeatAdaptedIntegralClosure.integral m hm T hT (curveInput m hm T hT) +
        secondChannel m T (constantInput m hm T hT).val)) :=
    hsum.congr' (Eventually.of_forall (fun n => (native_identity n m hm T hT).symm))
  exact tendsto_nhds_unique tendsto_const_nhds hconst

theorem actual_signed_identity (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (G : Cylinder) :
    ((HigherHeatAdaptedIntegralClosure.integral m hm T hT (curveInput m hm T hT) (core G) +
      HigherHeatAdaptedIntegralClosure.integral m hm T hT (curveInput m hm T hT) (core G) +
      secondChannel m T (constantInput m hm T hT).val (core G) : ℝ) : ℂ) =
        cylindricalExpectation m hm T hT (terminalCylinder^2 * G) := by
  have he := congrArg (fun φ : Dual => (φ (core G) : ℂ)) (quadratic_ito m hm T hT)
  exact he.symm.trans (pairing_core_complex m hm T hT (terminalCylinder^2) G)

theorem quadratic_order_two_drift (T : ℝ≥0) (hT : 0 < T) :
    secondChannel 1 T (constantField 1 (by norm_num) T hT) =
      ((2:ℝ)*(T:ℝ)) • pairing 1 (by norm_num) T hT (core (1:Cylinder)) := by
  apply ContinuousLinearMap.ext
  intro G
  change (coefficient 1 T * ((2*1-1:ℕ):ℝ)) *
    transpose timeMeasure (2*1-2) (constantField 1 (by norm_num) T hT) G = _
  rw [transpose_apply]
  have hi : (∫ t : ℝ, constantField 1 (by norm_num) T hT t G ∂timeMeasure) =
      pairing 1 (by norm_num) T hT (core (1:Cylinder)) G := by
    calc
      _ = ∫ _t : ℝ, pairing 1 (by norm_num) T hT (core (1:Cylinder)) G ∂timeMeasure :=
        integral_congr_ae ((constantField_ae 1 (by norm_num) T hT).mono
          (fun _ ht => congrArg (fun φ : Dual => φ G) ht))
      _ = _ := by rw [integral_const, time_mass]; exact one_smul ℝ _
  change (coefficient 1 T * ((2*1-1:ℕ):ℝ)) *
    (∫ t : ℝ, constantField 1 (by norm_num) T hT t G ∂timeMeasure) = _
  rw [hi]
  norm_num [coefficient]

theorem higher_quadratic_drift_zero (m : ℕ) (hm : 1 < m) :
    Polynomial.derivative^[2*m] ((Polynomial.X : Polynomial ℝ)^2) = 0 := by
  rw [Polynomial.iterate_derivative_X_pow_eq_smul,
    Nat.descFactorial_eq_zero_iff_lt.mpr (show 2 < 2*m by omega), Nat.cast_zero, zero_smul]

end OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticIto
