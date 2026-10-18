import Foundation.HigherHeatDyadicDualData
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! A unique norm-Lipschitz, Borel measurable signed dual coordinate curve on all normalized times.
This weak observable realization does not construct a chronological stochastic integral. -/
noncomputable section
open scoped NNReal Topology

namespace OperatorDerivativeRewrite.Foundation.HigherHeatContinuousDualCoordinate
open HigherHeatDyadicTimeDensity HigherHeatDyadicDualData HigherHeatDyadicDualNodes
open HigherHeatPolynomialCylinders HigherHeatPolynomialPathDomain HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatPairedDualCausality

def curve (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : C(Interval, Dual) :=
  ⟨dyadicSet_dense.extend (data m hm T hT),
    (dyadicSet_dense.uniformContinuous_extend (data_lipschitz m hm T hT).uniformContinuous).continuous⟩

theorem curve_lipschitz (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    LipschitzWith (constant m T) (curve m hm T hT) :=
  dyadicSet_dense.lipschitzWith_extend (data_lipschitz m hm T hT)

theorem curve_node (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (o : Option (Fin (size n))) :
    curve m hm T hT (node n o) = dualNode m hm T hT n o := by
  change dyadicSet_dense.extend (data m hm T hT) (node n o) = _
  rw [dyadicSet_dense.extend_eq (data_lipschitz m hm T hT).continuous ⟨node n o, n, o, rfl⟩]
  exact data_node m hm T hT n o

def zeroTime : Interval := ⟨0, le_rfl, zero_le_one⟩

theorem curve_zero (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    curve m hm T hT zeroTime = 0 := by
  change curve m hm T hT (node 0 none) = _
  rw [curve_node]
  rfl

theorem curve_unique (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (f : C(Interval, Dual))
    (hf : ∀ n o, f (node n o) = dualNode m hm T hT n o) : f = curve m hm T hT := by
  apply ContinuousMap.coe_injective
  apply dyadicSet_dense.denseRange_val.equalizer f.continuous (curve m hm T hT).continuous
  funext t
  change f t.val = curve m hm T hT t.val
  obtain ⟨n, o, ht⟩ := t.property
  rw [← ht, hf, curve_node]

theorem curve_core_pairing (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (i : Fin (size n)) (F : Cylinder) :
    (curve m hm T hT (node n (some i)) (core F):ℂ) =
      cylindricalExpectation m hm T hT (positionCylinder n i * F) := by
  rw [curve_node]
  exact pairing_core_complex m hm T hT (positionCylinder n i) F

theorem curve_borel_measurable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    @Measurable Interval Dual (borel Interval) (borel Dual) (curve m hm T hT) := by
  letI : MeasurableSpace Interval := borel Interval
  letI : MeasurableSpace Dual := borel Dual
  letI : BorelSpace Interval := ⟨rfl⟩
  letI : BorelSpace Dual := ⟨rfl⟩
  exact (curve m hm T hT).continuous.measurable

theorem curve_in_core_closure (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (t : Interval) :
    curve m hm T hT t ∈ closure (Set.range (fun F : Cylinder => pairing m hm T hT (core F))) := by
  have hc : IsClosed {s : Interval | curve m hm T hT s ∈
      closure (Set.range (fun F : Cylinder => pairing m hm T hT (core F)))} :=
    isClosed_closure.preimage (curve m hm T hT).continuous
  have hd : dyadicSet ⊆ {s : Interval | curve m hm T hT s ∈
      closure (Set.range (fun F : Cylinder => pairing m hm T hT (core F)))} := by
    rintro s ⟨n, o, rfl⟩
    change curve m hm T hT (node n o) ∈
      closure (Set.range (fun F : Cylinder => pairing m hm T hT (core F)))
    rw [curve_node]
    apply subset_closure
    cases o with
    | none =>
      refine ⟨0, ?_⟩
      change pairing m hm T hT (core (0:Cylinder)) = (0:Dual)
      rw [map_zero, map_zero]
    | some i => exact ⟨positionCylinder n i, rfl⟩
  exact (closure_minimal hd hc) (dyadicSet_dense t)

end OperatorDerivativeRewrite.Foundation.HigherHeatContinuousDualCoordinate
