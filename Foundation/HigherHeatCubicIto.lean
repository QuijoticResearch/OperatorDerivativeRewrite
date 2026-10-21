import Foundation.HigherHeatQuadraticPredictableField
import Foundation.HigherHeatQuadraticIto

/-! An actual three-channel terminal-cubic signed Itô identity.
All predictable coefficient fields and native-sum limits are constructed. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCubicIto
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatPairedDualCausality HigherHeatWeakTimeAdjoint
open HigherHeatQuadraticItoData HigherHeatQuadraticItoFields HigherHeatQuadraticItoApproximation
open HigherHeatQuadraticPredictableField HigherHeatCubicChannelLimit HigherHeatSecondChannelSteps
open HigherHeatThirdChannelSteps HigherHeatDyadicStepAgreement HigherHeatAdaptedStepDuality

theorem cubic_telescope (n : ℕ) :
    (HigherHeatMultivariateMoments.terminal : Test n)^3 =
      (3:ℕ) • stepPolynomial (squarePast n) +
      (3:ℕ) • HigherHeatQuadraticChannelLimit.quadraticPolynomial n (past n) +
      cubicPolynomial n (fun _ => 1) := by
  have ht := Finset.sum_range_sub (fun c => (prefixPolynomial n c)^3) (size n)
  have hf := Fin.sum_univ_eq_sum_range
    (fun c => (prefixPolynomial n (c+1))^3-(prefixPolynomial n c)^3) (size n)
  have hs : (∑ j : Fin (size n),
      ((prefixPolynomial n (j.val+1))^3-(prefixPolynomial n j.val)^3)) =
      (HigherHeatMultivariateMoments.terminal : Test n)^3 := by
    rw [hf, ht, prefix_end, prefix_zero, zero_pow (by norm_num : (3:ℕ) ≠ 0), sub_zero]
  have he (j : Fin (size n)) :
      (prefixPolynomial n (j.val+1))^3-(prefixPolynomial n j.val)^3 =
        (3:ℕ) • ((past n j)^2*MvPolynomial.X j) +
        (3:ℕ) • (past n j*(MvPolynomial.X j)^2) + (MvPolynomial.X j)^3 := by
    rw [prefix_succ n j.val j.isLt]
    change (past n j+MvPolynomial.X j)^3-(past n j)^3 = _
    simp only [nsmul_eq_mul]
    ring
  simp only [he, Finset.sum_add_distrib, ← Finset.smul_sum] at hs
  simpa only [stepPolynomial, squarePast, HigherHeatQuadraticChannelLimit.quadraticPolynomial,
    cubicPolynomial, one_mul] using hs.symm

theorem native_identity (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    pairing 2 (by norm_num) T hT (core (terminalCylinder^3)) =
      (3:ℕ) • firstChannel 2 T (adaptedField n 2 (by norm_num) T hT (squarePast n)) +
      (3:ℕ) • pairing 2 (by norm_num) T hT
        (core (cylinderOf n (HigherHeatQuadraticChannelLimit.quadraticPolynomial n (past n)))) +
      pairing 2 (by norm_num) T hT (core (cylinderOf n (cubicPolynomial n (fun _ => 1)))) := by
  have hc : terminalCylinder^3 =
      cylinderOf n ((HigherHeatMultivariateMoments.terminal : Test n)^3) := by
    rw [HigherHeatTerminalPositions.terminal_on_grid n, map_pow]
  have hs := HigherHeatCompletedStepAgreement.adapted_sum_dual n 2 (by norm_num) T hT
    (squarePast n) (squarePast_adapted n)
  rw [hc, cubic_telescope]
  simp only [map_add, map_nsmul, ← hs]

theorem square_linear_steps_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => firstChannel 2 T (adaptedField n 2 (by norm_num) T hT (squarePast n)))
      atTop (𝓝 (HigherHeatAdaptedIntegralClosure.integral 2 (by norm_num) T hT
        (quadraticInput T hT))) := by
  change Tendsto _ atTop (𝓝 (firstChannel 2 T (quadraticField T hT)))
  exact ((firstChannel 2 T).continuous.tendsto (quadraticField T hT)).comp (fields_tendsto T hT)

theorem past_quadratic_steps_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => pairing 2 (by norm_num) T hT
      (core (cylinderOf n (HigherHeatQuadraticChannelLimit.quadraticPolynomial n (past n)))))
      atTop (𝓝 (secondChannel 2 T (curveField 2 (by norm_num) T hT))) := by
  have hM (n : ℕ) (j : Fin (size n)) :
      ‖pairing 2 (by norm_num) T hT (core (cylinderOf n (past n j)))‖ ≤
        ‖HigherHeatContinuousDualCoordinate.curve 2 (by norm_num) T hT‖ := by
    rw [past_curve]
    exact (HigherHeatContinuousDualCoordinate.curve 2 (by norm_num) T hT).norm_coe_le_norm _
  exact HigherHeatQuadraticChannelLimit.quadratic_sums_converge 2 (by norm_num) T hT
    (fun n => past n) past_adapted
    ‖HigherHeatContinuousDualCoordinate.curve 2 (by norm_num) T hT‖ hM
    (curveInput 2 (by norm_num) T hT) (past_fields_tendsto 2 (by norm_num) T hT)

theorem cubic_ito (T : ℝ≥0) (hT : 0 < T) :
    pairing 2 (by norm_num) T hT (core (terminalCylinder^3)) =
      (3:ℕ) • HigherHeatAdaptedIntegralClosure.integral 2 (by norm_num) T hT
        (quadraticInput T hT) +
      (3:ℕ) • secondChannel 2 T (curveField 2 (by norm_num) T hT) +
      thirdChannel T (constantField 2 (by norm_num) T hT) := by
  let : ContinuousAdd Dual := (inferInstance : IsTopologicalAddGroup Dual).toContinuousAdd
  have h₁ := square_linear_steps_tendsto T hT
  have h₂ := past_quadratic_steps_tendsto T hT
  have h₃ := constant_cubic_sums_converge T hT
  have hs := ((h₁.const_smul (3:ℕ)).add (h₂.const_smul (3:ℕ))).add h₃
  have hc := hs.congr' (Eventually.of_forall (fun n => (native_identity n T hT).symm))
  exact tendsto_nhds_unique tendsto_const_nhds hc

theorem actual_signed_identity (T : ℝ≥0) (hT : 0 < T) (G : Cylinder) :
    (((3:ℝ)*HigherHeatAdaptedIntegralClosure.integral 2 (by norm_num) T hT
          (quadraticInput T hT) (core G) +
      (3:ℝ)*secondChannel 2 T (curveField 2 (by norm_num) T hT) (core G) +
      thirdChannel T (constantField 2 (by norm_num) T hT) (core G) : ℝ) : ℂ) =
        cylindricalExpectation 2 (by norm_num) T hT (terminalCylinder^3*G) := by
  have he := congrArg (fun φ : Dual => (φ (core G) : ℂ)) (cubic_ito T hT)
  have hh : (((3:ℝ)*HigherHeatAdaptedIntegralClosure.integral 2 (by norm_num) T hT
          (quadraticInput T hT) (core G) +
      (3:ℝ)*secondChannel 2 T (curveField 2 (by norm_num) T hT) (core G) +
      thirdChannel T (constantField 2 (by norm_num) T hT) (core G) : ℝ) : ℂ) =
      (pairing 2 (by norm_num) T hT (core (terminalCylinder^3)) (core G) : ℂ) := by
    simpa only [add_apply, smul_apply, nsmul_eq_mul, Nat.cast_ofNat] using he.symm
  exact hh.trans (pairing_core_complex 2 (by norm_num) T hT (terminalCylinder^3) G)

end OperatorDerivativeRewrite.Foundation.HigherHeatCubicIto
