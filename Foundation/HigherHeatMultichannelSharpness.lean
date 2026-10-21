import Foundation.HigherHeatCompletedSignedApproximation
import Foundation.HigherHeatFirstChannelRange

/-! Every even-order reconstruction needs its final stochastic channel:
the centered terminal power p-1 separates it from all lower channels. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatMultichannelSharpness
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatPairedDualCausality HigherHeatWeakTimeAdjoint
open HigherHeatAllChannelNormalization HigherHeatFirstChannelRange HigherHeatTerminalPositions

theorem lower_channel_terminal_zero (m : ℕ) (T : ℝ≥0) (r : ℕ) (hr : r+2 < 2*m)
    (A : Field timeMeasure) : channel m T r A (core terminalCylinder) = 0 := by
  rw [HigherHeatCompletedClarkOcone.channel_duality]
  have hz (t : ℝ) : ((HigherHeatTimeDerivative.atTime t)^(2*m-1-r))
      (core terminalCylinder) = 0 := by
    rw [← terminal_coordinate]
    exact atTime_pow_coordinate_zero t 0 (HigherHeatTerminalPositions.lastIndex 0)
      (2*m-1-r) (by omega)
  simp only [hz, map_zero, MeasureTheory.integral_zero, mul_zero]

theorem all_lower_channels_insufficient (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Fin (2*m-2) → Field timeMeasure) :
    (∑ r : Fin (2*m-2), channel m T r.val (A r)) ≠
      pairing m hm T hT (core (terminalCylinder^(2*m-1))) := by
  intro he
  have h := congrArg (fun φ : Dual => φ (core terminalCylinder)) he
  have hz : (∑ r : Fin (2*m-2), channel m T r.val (A r)) (core terminalCylinder) = 0 := by
    simp only [sum_apply]
    apply Finset.sum_eq_zero
    intro r _
    exact lower_channel_terminal_zero m T r.val (by have := r.isLt; omega) (A r)
  rw [hz, witness_pairing m hm T hT] at h
  have hn : ((2*m).factorial:ℝ)*((-1:ℝ)^(m+1)*(T:ℝ)) ≠ 0 :=
    mul_ne_zero (by positivity)
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (by exact_mod_cast hT)))
  exact hn h.symm

theorem witness_mean_zero (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    HigherHeatCompletedSignedMean.mean m hm T hT (core (terminalCylinder^(2*m-1))) = 0 :=
  witness_centered m hm T hT

end OperatorDerivativeRewrite.Foundation.HigherHeatMultichannelSharpness
