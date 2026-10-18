import Foundation.HigherHeatDyadicTimeDensity

/-! Presentation-independent signed dual data on the dense dyadic time set. -/
noncomputable section
open scoped NNReal Topology

namespace OperatorDerivativeRewrite.Foundation.HigherHeatDyadicDualData
open HigherHeatDyadicTimeDensity HigherHeatDyadicDualNodes HigherHeatPairedDualCausality
open HigherHeatPolynomialCylinders HigherHeatContinuousCylinders

def representation (t : dyadicSet) : (n : ℕ) × Option (Fin (size n)) :=
  ⟨Classical.choose t.property, Classical.choose (Classical.choose_spec t.property)⟩

theorem representation_time (t : dyadicSet) :
    node (representation t).1 (representation t).2 = t.val :=
  Classical.choose_spec (Classical.choose_spec t.property)

def data (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (t : dyadicSet) : Dual :=
  dualNode m hm T hT (representation t).1 (representation t).2

theorem data_node (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (o : Option (Fin (size n))) :
    data m hm T hT ⟨node n o, n, o, rfl⟩ = dualNode m hm T hT n o := by
  apply dualNode_same_time
  exact congrArg Subtype.val (representation_time ⟨node n o, n, o, rfl⟩)

def constant (m : ℕ) (T : ℝ≥0) : ℝ≥0 :=
  ⟨((2*m:ℕ):ℝ)*(T:ℝ)*Real.exp (T:ℝ), by positivity⟩

theorem data_lipschitz (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    LipschitzWith (constant m T) (data m hm T hT) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  change dist (data m hm T hT a) (data m hm T hT b) ≤
    (((2*m:ℕ):ℝ)*(T:ℝ)*Real.exp (T:ℝ)) * dist a b
  have hb := dualNode_bound m hm T hT (representation a).1 (representation b).1
    (representation a).2 (representation b).2
  have ha := congrArg Subtype.val (representation_time a)
  have hc := congrArg Subtype.val (representation_time b)
  change interpolationNode (representation a).1 (representation a).2 = (a.val:ℝ) at ha
  change interpolationNode (representation b).1 (representation b).2 = (b.val:ℝ) at hc
  rw [ha, hc] at hb
  have he : dist (data m hm T hT a) (data m hm T hT b) =
      ‖data m hm T hT a-data m hm T hT b‖ :=
    dist_eq_norm (data m hm T hT a) (data m hm T hT b)
  rw [he]
  simpa only [data, constant, NNReal.coe_mk, dist_eq_norm, Real.norm_eq_abs,
    Subtype.dist_eq] using hb

end OperatorDerivativeRewrite.Foundation.HigherHeatDyadicDualData
