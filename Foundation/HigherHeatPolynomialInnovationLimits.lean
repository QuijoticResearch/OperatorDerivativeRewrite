import Foundation.HigherHeatCenteredPowerLimits
import Foundation.HigherHeatPolynomialPredictableField

/-! Unconditional signed innovation limits for all polynomial past coefficients.
Uniform coefficient bounds and genuine L1 convergence are discharged, not assumed. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialInnovationLimits
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatPairedDualCausality HigherHeatWeakTimeAdjoint
open HigherHeatDyadicStepAgreement HigherHeatAllChannelNormalization
open HigherHeatPolynomialPredictableField HigherHeatPolynomialCurveAgreement
open HigherHeatCenteredPowerLimits

theorem past_power_innovation_limit (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (d r : ℕ) :
    Tendsto (fun n => pairing m hm T hT
      (core (cylinderOf n (centeredPower n m T (r+1) (powerPast n d))))) atTop
      (𝓝 (if r+1 < 2*m then channel m T r (powerField m hm T hT d) else (0:Dual))) := by
  have hM := fun n j => powerPast_bound n m hm T hT d j
  by_cases hr : r+1 < 2*m
  · rw [if_pos hr]
    exact low_centered_converge m hm T hT (fun n => powerPast n d)
      (fun n => powerPast_adapted n d) r hr ‖coordinateCurve m hm T hT d‖ hM
      (powerField m hm T hT d) (fields_tendsto m hm T hT d)
  · rw [if_neg hr]
    by_cases he : r+1=2*m
    · simp_rw [he]
      exact critical_centered_vanish m hm T hT (fun n => powerPast n d)
        (fun n => powerPast_adapted n d) ‖coordinateCurve m hm T hT d‖ hM
    · exact higher_centered_vanish m hm T hT (fun n => powerPast n d)
        (fun n => powerPast_adapted n d) r (by omega) ‖coordinateCurve m hm T hT d‖ hM

theorem past_power_critical_rate (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (d : ℕ) :
    ‖pairing m hm T hT (core (cylinderOf n
      (centeredPower n m T (2*m) (powerPast n d))))‖ ≤
      HigherHeatAllPowerBounds.powerConstant m T (2*m)*
        (HigherHeatDyadicLaws.duration 1 n:ℝ)*‖coordinateCurve m hm T hT d‖ := by
  exact critical_centered_bound n m hm T hT (powerPast n d) (powerPast_adapted n d)
    ‖coordinateCurve m hm T hT d‖ (powerPast_bound n m hm T hT d)

end OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialInnovationLimits
