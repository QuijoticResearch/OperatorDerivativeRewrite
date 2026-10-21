import Foundation.HigherHeatInnovationMoments

/-! Centered signed innovations: exact drift cancellation and native norm limits.
The hypotheses concern actual adapted coefficients and their uniform dual bounds. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCenteredPowerLimits
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatPairedDualCausality HigherHeatWeakTimeAdjoint
open HigherHeatDyadicStepAgreement HigherHeatAdaptedStepDuality HigherHeatAllChannelLimit
open HigherHeatInnovationMoments HigherHeatAllChannelNormalization

def centeredPower (n m : ℕ) (T : ℝ≥0) (q : ℕ) (F : Fin (size n) → Test n) : Test n :=
  ∑ j, F j * ((MvPolynomial.X j)^q - MvPolynomial.C (cellMoment n m T q))

theorem centered_power_eq (n m : ℕ) (T : ℝ≥0) (q : ℕ) (F : Fin (size n) → Test n) :
    centeredPower n m T q F = powerPolynomial n q F - cellMoment n m T q • ∑ j, F j := by
  simp only [centeredPower, powerPolynomial, mul_sub, Finset.sum_sub_distrib,
    Finset.smul_sum, MvPolynomial.smul_eq_C_mul, mul_comm]

theorem low_centered_eq (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (q : ℕ)
    (hq : 0 < q) (hqp : q < 2*m) (F : Fin (size n) → Test n) :
    centeredPower n m T q F = powerPolynomial n q F := by
  rw [centered_power_eq, low_moment_zero n m hm T q hq hqp, zero_smul, sub_zero]

theorem critical_centered_eq (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) (hF : Adapted F) :
    pairing m hm T hT (core (cylinderOf n (centeredPower n m T (2*m) F))) =
      remainder n m hm T hT F (2*m-1) := by
  rw [centered_power_eq]
  simp only [map_sub, map_smul, map_sum]
  have hs := sum_identity n m hm T hT F hF (2*m-1) (by omega)
  rw [show 2*m-1+1=2*m by omega] at hs
  rw [hs]
  have hd : channel m T (2*m-1) (adaptedField n m hm T hT F) =
      cellMoment n m T (2*m) • ∑ j, pairing m hm T hT (core (cylinderOf n (F j))) := by
    simp only [adaptedField, map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ => drift_step n m hm T hT j (F j))
  rw [hd, add_sub_cancel_right]

theorem critical_centered_vanish (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : ∀ n, Fin (size n) → Test n) (hF : ∀ n, Adapted (F n)) (M : ℝ)
    (hM : ∀ n j, ‖pairing m hm T hT (core (cylinderOf n (F n j)))‖ ≤ M) :
    Tendsto (fun n => pairing m hm T hT
      (core (cylinderOf n (centeredPower n m T (2*m) (F n))))) atTop (𝓝 (0:Dual)) := by
  simp_rw [critical_centered_eq _ m hm T hT _ (hF _)]
  exact remainder_tendsto m hm T hT F hF (2*m-1) (by omega) M hM

theorem critical_centered_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) (hF : Adapted F) (M : ℝ)
    (hM : ∀ j, ‖pairing m hm T hT (core (cylinderOf n (F j)))‖ ≤ M) :
    ‖pairing m hm T hT (core (cylinderOf n (centeredPower n m T (2*m) F)))‖ ≤
      HigherHeatAllPowerBounds.powerConstant m T (2*m)*
        (HigherHeatDyadicLaws.duration 1 n:ℝ)*M := by
  rw [critical_centered_eq n m hm T hT F hF]
  simpa only [show 2*m-1+1=2*m by omega] using
    remainder_bound n m hm T hT F hF (2*m-1) (by omega) M hM

theorem actual_critical_probe_vanish (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : ∀ n, Fin (size n) → Test n) (hF : ∀ n, Adapted (F n)) (M : ℝ)
    (hM : ∀ n j, ‖pairing m hm T hT (core (cylinderOf n (F n j)))‖ ≤ M)
    (G : Cylinder) :
    Tendsto (fun n => cylindricalExpectation m hm T hT
      ((cylinderOf n (centeredPower n m T (2*m) (F n)))*G)) atTop (𝓝 (0:ℂ)) := by
  have h := ((ContinuousLinearMap.apply ℝ ℝ (core G)).continuous.tendsto (0:Dual)).comp
    (critical_centered_vanish m hm T hT F hF M hM)
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  change Tendsto (fun n => (pairing m hm T hT
    (core (cylinderOf n (centeredPower n m T (2*m) (F n)))) (core G) : ℂ))
      atTop (𝓝 (0:ℂ)) at hc
  simp_rw [pairing_core_complex] at hc
  exact hc

theorem low_centered_converge (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : ∀ n, Fin (size n) → Test n) (hF : ∀ n, Adapted (F n))
    (r : ℕ) (hr : r+1 < 2*m) (M : ℝ)
    (hM : ∀ n j, ‖pairing m hm T hT (core (cylinderOf n (F n j)))‖ ≤ M)
    (A : Field timeMeasure)
    (hA : Tendsto (fun n => adaptedField n m hm T hT (F n)) atTop (𝓝 A)) :
    Tendsto (fun n => pairing m hm T hT
      (core (cylinderOf n (centeredPower n m T (r+1) (F n))))) atTop
      (𝓝 (channel m T r A)) := by
  simp_rw [low_centered_eq _ m hm T (r+1) (by omega) hr]
  exact power_sums_converge m hm T hT F hF r (by omega) M hM A hA

theorem compensation_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : ℕ) (F : Fin (size n) → Test n) (C M : ℝ) (hC : 0 ≤ C)
    (hc : |cellMoment n m T q| ≤ C*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2)
    (hM : ∀ j, ‖pairing m hm T hT (core (cylinderOf n (F j)))‖ ≤ M) :
    ‖cellMoment n m T q • ∑ j, pairing m hm T hT (core (cylinderOf n (F j)))‖ ≤
      C*(HigherHeatDyadicLaws.duration 1 n:ℝ)*M := by
  rw [Finset.smul_sum]
  calc
    _ ≤ ∑ j, ‖cellMoment n m T q • pairing m hm T hT (core (cylinderOf n (F j)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin (size n), C*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2*M := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hM j) (mul_nonneg hC (sq_nonneg _)))
    _ = (size n:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*
        (C*(HigherHeatDyadicLaws.duration 1 n:ℝ)*M) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = _ := by rw [HigherHeatQuadraticChannelLimit.size_duration]; ring

theorem higher_centered_vanish (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : ∀ n, Fin (size n) → Test n) (hF : ∀ n, Adapted (F n))
    (r : ℕ) (hr : 2*m ≤ r) (M : ℝ)
    (hM : ∀ n j, ‖pairing m hm T hT (core (cylinderOf n (F n j)))‖ ≤ M) :
    Tendsto (fun n => pairing m hm T hT
      (core (cylinderOf n (centeredPower n m T (r+1) (F n))))) atTop (𝓝 (0:Dual)) := by
  obtain ⟨C, hC, hc⟩ := higher_moment_bound m hm T (r+1) (by omega)
  have hs : Tendsto (fun n => cellMoment n m T (r+1) •
      ∑ j, pairing m hm T hT (core (cylinderOf n (F n j)))) atTop (𝓝 (0:Dual)) := by
    apply (tendsto_zero_iff_norm_tendsto_zero (E := Dual)).mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => compensation_bound n m hm T hT (r+1) (F n) C M hC (hc n) (hM n))
    simpa using ((tendsto_const_nhds (x := C)).mul
      (HigherHeatEarlyDualContinuity.duration_tendsto 1)).mul (tendsto_const_nhds (x := M))
  have h := (higher_sums_vanish m hm T hT F hF r hr M hM).sub hs
  simpa only [centered_power_eq, map_sub, map_smul, map_sum, sub_zero] using h

end OperatorDerivativeRewrite.Foundation.HigherHeatCenteredPowerLimits
