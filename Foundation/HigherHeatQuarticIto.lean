import Foundation.HigherHeatCubicPredictableField
import Foundation.HigherHeatQuarticChannelLimit
import Foundation.HigherHeatCubicIto

/-! Actual signed quartic Itô identity. All native sums converge in completed-dual
norm, including the fourth-power drift; every predictable field is constructed. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatQuarticIto
open MeasureTheory Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatPairedDualCausality HigherHeatWeakTimeAdjoint
open HigherHeatQuadraticItoData HigherHeatQuadraticItoFields HigherHeatQuadraticItoApproximation
open HigherHeatQuadraticPredictableField HigherHeatCubicPredictableField
open HigherHeatCubicChannelLimit HigherHeatQuarticChannelLimit HigherHeatSecondChannelSteps
open HigherHeatThirdChannelSteps HigherHeatFourthChannelSteps HigherHeatDyadicStepAgreement
open HigherHeatAdaptedStepDuality

theorem quartic_telescope (n : ℕ) :
    (HigherHeatMultivariateMoments.terminal : Test n)^4 =
      (4:ℕ) • stepPolynomial (cubePast n) +
      (6:ℕ) • HigherHeatQuadraticChannelLimit.quadraticPolynomial n (squarePast n) +
      (4:ℕ) • cubicPolynomial n (past n) + quarticPolynomial n (fun _ => 1) := by
  have ht := Finset.sum_range_sub (fun c => (prefixPolynomial n c)^4) (size n)
  have hf := Fin.sum_univ_eq_sum_range
    (fun c => (prefixPolynomial n (c+1))^4-(prefixPolynomial n c)^4) (size n)
  have hs : (∑ j : Fin (size n),
      ((prefixPolynomial n (j.val+1))^4-(prefixPolynomial n j.val)^4)) =
      (HigherHeatMultivariateMoments.terminal : Test n)^4 := by
    rw [hf, ht, prefix_end, prefix_zero, zero_pow (by norm_num : (4:ℕ) ≠ 0), sub_zero]
  have he (j : Fin (size n)) :
      (prefixPolynomial n (j.val+1))^4-(prefixPolynomial n j.val)^4 =
        (4:ℕ) • ((past n j)^3*MvPolynomial.X j) +
        (6:ℕ) • ((past n j)^2*(MvPolynomial.X j)^2) +
        (4:ℕ) • (past n j*(MvPolynomial.X j)^3) + (MvPolynomial.X j)^4 := by
    rw [prefix_succ n j.val j.isLt]
    change (past n j+MvPolynomial.X j)^4-(past n j)^4 = _
    simp only [nsmul_eq_mul]
    ring
  simp only [he, Finset.sum_add_distrib, ← Finset.smul_sum] at hs
  simpa only [stepPolynomial, cubePast, squarePast,
    HigherHeatQuadraticChannelLimit.quadraticPolynomial, cubicPolynomial,
    quarticPolynomial, one_mul] using hs.symm

theorem native_identity (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    pairing 2 (by norm_num) T hT (core (terminalCylinder^4)) =
      (4:ℕ) • firstChannel 2 T (adaptedField n 2 (by norm_num) T hT (cubePast n)) +
      (6:ℕ) • pairing 2 (by norm_num) T hT
        (core (cylinderOf n (HigherHeatQuadraticChannelLimit.quadraticPolynomial n (squarePast n)))) +
      (4:ℕ) • pairing 2 (by norm_num) T hT
        (core (cylinderOf n (cubicPolynomial n (past n)))) +
      pairing 2 (by norm_num) T hT (core (cylinderOf n (quarticPolynomial n (fun _ => 1)))) := by
  have hc : terminalCylinder^4 =
      cylinderOf n ((HigherHeatMultivariateMoments.terminal : Test n)^4) := by
    rw [HigherHeatTerminalPositions.terminal_on_grid n, map_pow]
  have hs := HigherHeatCompletedStepAgreement.adapted_sum_dual n 2 (by norm_num) T hT
    (cubePast n) (cubePast_adapted n)
  rw [hc, quartic_telescope]
  simp only [map_add, map_nsmul, ← hs]

theorem cube_linear_steps_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => firstChannel 2 T (adaptedField n 2 (by norm_num) T hT (cubePast n)))
      atTop (𝓝 (HigherHeatAdaptedIntegralClosure.integral 2 (by norm_num) T hT
        (cubicInput T hT))) := by
  change Tendsto _ atTop (𝓝 (firstChannel 2 T (cubicField T hT)))
  exact ((firstChannel 2 T).continuous.tendsto (cubicField T hT)).comp
    (HigherHeatCubicPredictableField.fields_tendsto T hT)

theorem square_quadratic_steps_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => pairing 2 (by norm_num) T hT
      (core (cylinderOf n (HigherHeatQuadraticChannelLimit.quadraticPolynomial n (squarePast n)))))
      atTop (𝓝 (secondChannel 2 T (quadraticField T hT))) := by
  exact HigherHeatQuadraticChannelLimit.quadratic_sums_converge 2 (by norm_num) T hT
    (fun n => squarePast n) squarePast_adapted
    ‖HigherHeatQuadraticDualCurve.quadraticCurve T hT‖ (fun n j => squarePast_bound n T hT j)
    (quadraticInput T hT) (HigherHeatQuadraticPredictableField.fields_tendsto T hT)

theorem past_cubic_steps_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => pairing 2 (by norm_num) T hT
      (core (cylinderOf n (cubicPolynomial n (past n)))))
      atTop (𝓝 (thirdChannel T (curveField 2 (by norm_num) T hT))) := by
  have hM (n : ℕ) (j : Fin (size n)) :
      ‖pairing 2 (by norm_num) T hT (core (cylinderOf n (past n j)))‖ ≤
        ‖HigherHeatContinuousDualCoordinate.curve 2 (by norm_num) T hT‖ := by
    rw [past_curve]
    exact (HigherHeatContinuousDualCoordinate.curve 2 (by norm_num) T hT).norm_coe_le_norm _
  exact cubic_sums_converge T hT (fun n => past n) past_adapted
    ‖HigherHeatContinuousDualCoordinate.curve 2 (by norm_num) T hT‖ hM
    (curveField 2 (by norm_num) T hT) (past_fields_tendsto 2 (by norm_num) T hT)

theorem fourth_constant (T : ℝ≥0) (hT : 0 < T) :
    fourthChannel T (constantField 2 (by norm_num) T hT) =
      (-24*(T:ℝ)) • pairing 2 (by norm_num) T hT (core (1:Cylinder)) := by
  apply ContinuousLinearMap.ext
  intro G
  change (6*coefficient 2 T) * transpose timeMeasure 0
    (constantField 2 (by norm_num) T hT) G =
      (-24*(T:ℝ)) * pairing 2 (by norm_num) T hT (core (1:Cylinder)) G
  rw [transpose_apply]
  have he : (∫ t : ℝ, constantField 2 (by norm_num) T hT t
      (((HigherHeatTimeDerivative.atTime t)^0) G) ∂timeMeasure) =
      pairing 2 (by norm_num) T hT (core (1:Cylinder)) G := by
    calc
      _ = ∫ _t : ℝ, pairing 2 (by norm_num) T hT (core (1:Cylinder)) G ∂timeMeasure := by
        apply integral_congr_ae
        filter_upwards [constantField_ae 2 (by norm_num) T hT] with t ht
        rw [ht]
        rfl
      _ = _ := by simp [timeMeasure]
  rw [he]
  have hc : 6*coefficient 2 T = -24*(T:ℝ) := by
    norm_num [coefficient] <;> ring
  rw [hc]

theorem quartic_ito (T : ℝ≥0) (hT : 0 < T) :
    pairing 2 (by norm_num) T hT (core (terminalCylinder^4)) =
      (4:ℕ) • HigherHeatAdaptedIntegralClosure.integral 2 (by norm_num) T hT (cubicInput T hT) +
      (6:ℕ) • secondChannel 2 T (quadraticField T hT) +
      (4:ℕ) • thirdChannel T (curveField 2 (by norm_num) T hT) +
      (-24*(T:ℝ)) • pairing 2 (by norm_num) T hT (core (1:Cylinder)) := by
  let : ContinuousAdd Dual := (inferInstance : IsTopologicalAddGroup Dual).toContinuousAdd
  have h₁ := cube_linear_steps_tendsto T hT
  have h₂ := square_quadratic_steps_tendsto T hT
  have h₃ := past_cubic_steps_tendsto T hT
  have h₄ := constant_quartic_sums_converge T hT
  rw [fourth_constant T hT] at h₄
  have hs := (((h₁.const_smul (4:ℕ)).add (h₂.const_smul (6:ℕ))).add
    (h₃.const_smul (4:ℕ))).add h₄
  have hc := hs.congr' (Eventually.of_forall (fun n => (native_identity n T hT).symm))
  exact tendsto_nhds_unique tendsto_const_nhds hc

theorem centered_quartic (T : ℝ≥0) (hT : 0 < T) :
    pairing 2 (by norm_num) T hT (core (terminalCylinder^4)) +
      (24*(T:ℝ)) • pairing 2 (by norm_num) T hT (core (1:Cylinder)) =
      (4:ℕ) • HigherHeatAdaptedIntegralClosure.integral 2 (by norm_num) T hT (cubicInput T hT) +
      (6:ℕ) • secondChannel 2 T (quadraticField T hT) +
      (4:ℕ) • thirdChannel T (curveField 2 (by norm_num) T hT) := by
  apply ContinuousLinearMap.ext
  intro G
  have he := congrArg (fun φ : Dual => φ G) (quartic_ito T hT)
  simp only [add_apply, smul_apply, nsmul_eq_mul, smul_eq_mul] at he ⊢
  linarith [he]

theorem actual_signed_identity (T : ℝ≥0) (hT : 0 < T) (G : Cylinder) :
    (((4:ℝ)*HigherHeatAdaptedIntegralClosure.integral 2 (by norm_num) T hT
          (cubicInput T hT) (core G) +
      (6:ℝ)*secondChannel 2 T (quadraticField T hT) (core G) +
      (4:ℝ)*thirdChannel T (curveField 2 (by norm_num) T hT) (core G) +
      (-24*(T:ℝ))*pairing 2 (by norm_num) T hT (core (1:Cylinder)) (core G) : ℝ) : ℂ) =
        cylindricalExpectation 2 (by norm_num) T hT (terminalCylinder^4*G) := by
  have he := congrArg (fun φ : Dual => (φ (core G) : ℂ)) (quartic_ito T hT)
  have hh : (((4:ℝ)*HigherHeatAdaptedIntegralClosure.integral 2 (by norm_num) T hT
          (cubicInput T hT) (core G) +
      (6:ℝ)*secondChannel 2 T (quadraticField T hT) (core G) +
      (4:ℝ)*thirdChannel T (curveField 2 (by norm_num) T hT) (core G) +
      (-24*(T:ℝ))*pairing 2 (by norm_num) T hT (core (1:Cylinder)) (core G) : ℝ) : ℂ) =
      (pairing 2 (by norm_num) T hT (core (terminalCylinder^4)) (core G) : ℂ) := by
    simpa only [add_apply, smul_apply, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul] using he.symm
  exact hh.trans (pairing_core_complex 2 (by norm_num) T hT (terminalCylinder^4) G)

end OperatorDerivativeRewrite.Foundation.HigherHeatQuarticIto
