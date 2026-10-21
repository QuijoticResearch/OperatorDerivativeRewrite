import Foundation.HigherHeatPolynomialDualCurve
import Foundation.HigherHeatQuadraticDualCurve

/-! Genuine native agreement of the continuous dual power curves, all degrees/orders. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialCurveAgreement
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatPairedDualCausality HigherHeatPolynomialDualCurve
open HigherHeatPrefixPowerIdentity HigherHeatQuadraticItoData HigherHeatDyadicTimeDensity
open HigherHeatAllProductChannels

def coordinateCurve (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) : C(Interval,Dual) :=
  powerCurve m T (pairing m hm T hT (core (1:Cylinder))) r

def coordinateConstant (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) : ℝ≥0 :=
  HigherHeatPolynomialDualCurve.powerConstant m T (pairing m hm T hT (core (1:Cylinder))) r

theorem coordinate_curve_lipschitz (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    LipschitzWith (coordinateConstant m hm T hT r) (coordinateCurve m hm T hT r) :=
  powerFunction_lipschitz_with m T _ r

theorem coordinate_curve_prefix (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (c : ℕ) (hc : c ≤ size n) (r : ℕ) :
    coordinateCurve m hm T hT r (node n (prefixNode n c hc)) =
      pairing m hm T hT (core (cylinderOf n ((prefixPolynomial n c)^r))) := by
  change powerFunction m T (pairing m hm T hT (core (1:Cylinder))) r
    (node n (prefixNode n c hc)) = _
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => rw [powerFunction, pow_zero, map_one (cylinderOf n)]
    | succ r =>
      rw [powerFunction, prefix_power_identity n m hm T hT c hc r]
      apply Finset.sum_congr rfl
      intro k _
      rw [ih (r-k) (by omega), HigherHeatQuadraticDualCurve.prefix_time]

end OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialCurveAgreement
