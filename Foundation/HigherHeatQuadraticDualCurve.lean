import Foundation.HigherHeatPrefixSquareIdentity

/-! A genuine continuous quadratic signed-dual curve with exact native agreement. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticDualCurve
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatSecondChannelSteps HigherHeatPairedDualCausality
open HigherHeatPrefixFields HigherHeatPrefixSquareIdentity HigherHeatQuadraticItoData
open HigherHeatContinuousDualCoordinate HigherHeatDyadicTimeDensity HigherHeatDyadicDualNodes
open HigherHeatPolynomialPathDomain

def coordinatePrefix (T : ℝ≥0) (hT : 0 < T) (t : Interval) : Field timeMeasure :=
  segment 0 (t:ℝ) (curve 2 (by norm_num) T hT t)

theorem coordinate_prefix_lipschitz (T : ℝ≥0) (hT : 0 < T) :
    LipschitzWith (HigherHeatDyadicDualData.constant 2 T + ‖curve 2 (by norm_num) T hT‖₊)
      (coordinatePrefix T hT) :=
  prefix_lipschitz _ _ _ (curve_lipschitz 2 (by norm_num) T hT)
    (fun t => (curve 2 (by norm_num) T hT).norm_coe_le_norm t)

def constantPrefix (T : ℝ≥0) (hT : 0 < T) (t : Interval) : Field timeMeasure :=
  segment 0 (t:ℝ) (pairing 2 (by norm_num) T hT (core (1:Cylinder)))

theorem constant_prefix_lipschitz (T : ℝ≥0) (hT : 0 < T) :
    LipschitzWith ‖pairing 2 (by norm_num) T hT (core (1:Cylinder))‖₊ (constantPrefix T hT) := by
  unfold constantPrefix
  convert prefix_lipschitz
    (fun _ : Interval => pairing 2 (Nat.zero_lt_succ 1) T hT (core (1:Cylinder))) 0
    ‖pairing 2 (Nat.zero_lt_succ 1) T hT (core (1:Cylinder))‖₊
      (LipschitzWith.const _) (fun _ => le_rfl)
      using 1
  simp only [zero_add]

def quadraticCurve (T : ℝ≥0) (hT : 0 < T) : C(Interval, Dual) :=
  ⟨fun t => firstChannel 2 T (coordinatePrefix T hT t) + secondChannel 2 T (constantPrefix T hT t),
    ((firstChannel 2 T).continuous.comp (coordinate_prefix_lipschitz T hT).continuous).add
      ((secondChannel 2 T).continuous.comp (constant_prefix_lipschitz T hT).continuous)⟩

def quadraticConstant (T : ℝ≥0) (hT : 0 < T) : ℝ≥0 :=
  ‖firstChannel 2 T‖₊ *
      (HigherHeatDyadicDualData.constant 2 T + ‖curve 2 (by norm_num) T hT‖₊) +
    ‖secondChannel 2 T‖₊ * ‖pairing 2 (by norm_num) T hT (core (1:Cylinder))‖₊

theorem quadratic_curve_lipschitz (T : ℝ≥0) (hT : 0 < T) :
    LipschitzWith (quadraticConstant T hT) (quadraticCurve T hT) :=
  ((firstChannel 2 T).lipschitzWith.comp (coordinate_prefix_lipschitz T hT)).add
    ((secondChannel 2 T).lipschitzWith.comp (constant_prefix_lipschitz T hT))

theorem prefix_coordinate (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (c : ℕ) (hc : c ≤ size n) :
    pairing 2 (by norm_num) T hT (core (cylinderOf n (prefixPolynomial n c))) =
      curve 2 (by norm_num) T hT (node n (prefixNode n c hc)) := by
  rw [curve_node]
  by_cases hz : c=0
  · simp [hz, prefix_zero, prefixNode, dualNode]
  · let k : Fin (size n) := ⟨c-1, by omega⟩
    have hs : Finset.univ.filter (fun i : Fin (size n) => i.val < c) =
        Finset.univ.filter (fun i : Fin (size n) => i ≤ k) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change i.val < c ↔ i.val ≤ c-1
      omega
    have hp : cylinderOf n (prefixPolynomial n c) = positionCylinder n k := by
      unfold prefixPolynomial positionCylinder positionPolynomial
      rw [hs]
    rw [hp]
    simp only [prefixNode, dite_eq_right hz, dualNode, Option.elim_some]
    rfl

theorem prefix_time (n c : ℕ) (hc : c ≤ size n) :
    (node n (prefixNode n c hc):ℝ) = (c:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  change HigherHeatContinuousCylinders.interpolationNode n (prefixNode n c hc) = _
  rw [prefixNode_time]
  simp only [HigherHeatDyadicLaws.duration, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast]
  ring

theorem quadratic_curve_prefix (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (c : ℕ) (hc : c ≤ size n) :
    quadraticCurve T hT (node n (prefixNode n c hc)) =
      pairing 2 (by norm_num) T hT (core (cylinderOf n ((prefixPolynomial n c)^2))) := by
  change firstChannel 2 T (segment 0 (node n (prefixNode n c hc):ℝ)
      (curve 2 (by norm_num) T hT (node n (prefixNode n c hc)))) +
    secondChannel 2 T (segment 0 (node n (prefixNode n c hc):ℝ)
      (pairing 2 (by norm_num) T hT (core (1:Cylinder)))) = _
  rw [prefix_time, ← prefix_coordinate n T hT c hc]
  simpa only [map_one] using (prefix_square_identity n T hT c hc).symm

end OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticDualCurve
