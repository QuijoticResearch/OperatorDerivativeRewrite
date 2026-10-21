import Foundation.HigherHeatPolynomialItoData

/-! Actual signed Itô identities for every terminal monomial and even heat order.
All predictable fields and native-sum convergence hypotheses are discharged. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialIto
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatPairedDualCausality HigherHeatAllChannelNormalization
open HigherHeatAllChannelLimit HigherHeatPolynomialPredictableField HigherHeatPolynomialCurveAgreement
open HigherHeatPolynomialItoData HigherHeatAdaptedStepDuality

theorem native_power_sums_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (d q : ℕ) :
    Tendsto (fun n => pairing m hm T hT
      (core (cylinderOf n (powerPolynomial n (q+1) (powerPast n d))))) atTop
        (𝓝 (channel m T q (powerField m hm T hT d))) := by
  have hM (n : ℕ) (j : Fin (size n)) :
      ‖pairing m hm T hT (core (cylinderOf n (powerPast n d j)))‖ ≤
        ‖coordinateCurve m hm T hT d‖ := powerPast_bound n m hm T hT d j
  by_cases hq : q < 2*m
  · exact power_sums_converge m hm T hT (fun n => powerPast n d)
      (fun n => powerPast_adapted n d) q hq ‖coordinateCurve m hm T hT d‖ hM
      (powerField m hm T hT d) (fields_tendsto m hm T hT d)
  · have hq' : 2*m ≤ q := Nat.le_of_not_gt hq
    rw [channel_zero_above_order m T q hq', zero_apply]
    exact higher_sums_vanish m hm T hT (fun n => powerPast n d)
      (fun n => powerPast_adapted n d) q hq' ‖coordinateCurve m hm T hT d‖ hM

theorem power_ito (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (N : ℕ) :
    pairing m hm T hT (core (terminalCylinder^N-(0:Cylinder)^N)) =
      ∑ q ∈ Finset.range N, N.choose (q+1) • channel m T q
        (powerField m hm T hT (N-(q+1))) := by
  let : ContinuousAdd Dual := (inferInstance : IsTopologicalAddGroup Dual).toContinuousAdd
  have hs := tendsto_finsetSum (Finset.range N) (fun q _ =>
    (native_power_sums_tendsto m hm T hT (N-(q+1)) q).const_smul (N.choose (q+1)))
  have hc := hs.congr' (Eventually.of_forall (fun n => (native_identity n m hm T hT N).symm))
  exact tendsto_nhds_unique tendsto_const_nhds hc

theorem power_ito_channels (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (N : ℕ) :
    pairing m hm T hT (core (terminalCylinder^N-(0:Cylinder)^N)) =
      ∑ q ∈ Finset.range (2*m), N.choose (q+1) • channel m T q
        (powerField m hm T hT (N-(q+1))) := by
  rw [power_ito m hm T hT N]
  rcases le_total N (2*m) with h | h
  · apply Finset.sum_subset (Finset.range_mono h)
    intro q _ hq
    have hNq : N < q+1 := by simp only [Finset.mem_range] at hq; omega
    rw [Nat.choose_eq_zero_of_lt hNq, zero_nsmul]
  · symm
    apply Finset.sum_subset (Finset.range_mono h)
    intro q _ hq
    have hq' : 2*m ≤ q := by simp only [Finset.mem_range] at hq; omega
    rw [channel_zero_above_order m T q hq', zero_apply, smul_zero]

theorem actual_signed_identity (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (N : ℕ) (G : Cylinder) :
    (((∑ q ∈ Finset.range (2*m), N.choose (q+1) • channel m T q
        (powerField m hm T hT (N-(q+1)))) (core G):ℝ):ℂ) =
      cylindricalExpectation m hm T hT ((terminalCylinder^N-(0:Cylinder)^N)*G) := by
  have he := congrArg (fun φ : Dual => (φ (core G):ℂ)) (power_ito_channels m hm T hT N)
  exact he.symm.trans (pairing_core_complex m hm T hT _ G)

end OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialIto
