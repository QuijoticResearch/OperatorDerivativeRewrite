import Foundation.HigherHeatQuadraticDualCurve
import Foundation.HigherHeatPrefixCubeIdentity

/-! Continuous cubic signed-dual coordinates, identified with every native prefix.
The auxiliary prefix fields in the defining identity need not be adapted. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCubicDualCurve
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatSecondChannelSteps HigherHeatPairedDualCausality
open HigherHeatThirdChannelSteps HigherHeatPrefixFields HigherHeatQuadraticItoData
open HigherHeatContinuousDualCoordinate HigherHeatDyadicTimeDensity HigherHeatDyadicDualNodes
open HigherHeatQuadraticDualCurve HigherHeatPrefixCubeIdentity

def quadraticPrefix (T : ℝ≥0) (hT : 0 < T) (t : Interval) : Field timeMeasure :=
  segment 0 (t:ℝ) (quadraticCurve T hT t)

theorem quadratic_prefix_lipschitz (T : ℝ≥0) (hT : 0 < T) :
    LipschitzWith (quadraticConstant T hT + ‖quadraticCurve T hT‖₊)
      (quadraticPrefix T hT) :=
  prefix_lipschitz _ _ _ (quadratic_curve_lipschitz T hT)
    (fun t => (quadraticCurve T hT).norm_coe_le_norm t)

def cubicCurve (T : ℝ≥0) (hT : 0 < T) : C(Interval, Dual) :=
  ⟨fun t => firstChannel 2 T (quadraticPrefix T hT t) +
      (secondChannel 2 T (coordinatePrefix T hT t) +
        secondChannel 2 T (coordinatePrefix T hT t)) +
      thirdChannel T (constantPrefix T hT t),
    (((firstChannel 2 T).continuous.comp (quadratic_prefix_lipschitz T hT).continuous).add
      (((secondChannel 2 T).continuous.comp (coordinate_prefix_lipschitz T hT).continuous).add
        ((secondChannel 2 T).continuous.comp (coordinate_prefix_lipschitz T hT).continuous))).add
      ((thirdChannel T).continuous.comp (constant_prefix_lipschitz T hT).continuous)⟩

def cubicConstant (T : ℝ≥0) (hT : 0 < T) : ℝ≥0 :=
  ‖firstChannel 2 T‖₊ * (quadraticConstant T hT + ‖quadraticCurve T hT‖₊) +
    (‖secondChannel 2 T‖₊ *
        (HigherHeatDyadicDualData.constant 2 T + ‖curve 2 (by norm_num) T hT‖₊) +
      ‖secondChannel 2 T‖₊ *
        (HigherHeatDyadicDualData.constant 2 T + ‖curve 2 (by norm_num) T hT‖₊)) +
    ‖thirdChannel T‖₊ * ‖pairing 2 (by norm_num) T hT (core (1:Cylinder))‖₊

theorem cubic_curve_lipschitz (T : ℝ≥0) (hT : 0 < T) :
    LipschitzWith (cubicConstant T hT) (cubicCurve T hT) :=
  (((firstChannel 2 T).lipschitzWith.comp (quadratic_prefix_lipschitz T hT)).add
    (((secondChannel 2 T).lipschitzWith.comp (coordinate_prefix_lipschitz T hT)).add
      ((secondChannel 2 T).lipschitzWith.comp (coordinate_prefix_lipschitz T hT)))).add
    ((thirdChannel T).lipschitzWith.comp (constant_prefix_lipschitz T hT))

theorem cubic_curve_prefix (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (c : ℕ) (hc : c ≤ size n) :
    cubicCurve T hT (node n (prefixNode n c hc)) =
      pairing 2 (by norm_num) T hT (core (cylinderOf n ((prefixPolynomial n c)^3))) := by
  change firstChannel 2 T (segment 0 (node n (prefixNode n c hc):ℝ)
      (quadraticCurve T hT (node n (prefixNode n c hc)))) +
    (secondChannel 2 T (segment 0 (node n (prefixNode n c hc):ℝ)
        (curve 2 (by norm_num) T hT (node n (prefixNode n c hc)))) +
      secondChannel 2 T (segment 0 (node n (prefixNode n c hc):ℝ)
        (curve 2 (by norm_num) T hT (node n (prefixNode n c hc))))) +
    thirdChannel T (segment 0 (node n (prefixNode n c hc):ℝ)
      (pairing 2 (by norm_num) T hT (core (1:Cylinder)))) = _
  rw [quadratic_curve_prefix, prefix_time, ← prefix_coordinate n T hT c hc]
  simpa only [two_nsmul, map_one] using (prefix_cube_identity n T hT c hc).symm

end OperatorDerivativeRewrite.Foundation.HigherHeatCubicDualCurve
