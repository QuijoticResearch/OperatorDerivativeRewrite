import Foundation.IBMRightGermFiltration
import Mathlib.Topology.Order.AtTopBotIxx

/-! Strong L2 right continuity of the actual right-germ martingale, proved
by decreasing Hilbert projections over the entire right neighborhood. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRightGermContinuity
open IBMNaturalFiltrationObstruction IBMTimeAveragedObservable
open IBMIntrinsicRightGerm IBMRightGermFiltration
set_option backward.isDefEq.respectTransparency false

theorem rightPast_idempotent (t : ℝ≥0) :
    (⨅ u : Ioi t, rightPast u.val) = rightPast t := by
  apply le_antisymm
  · rw [rightPast_eq_iInf t]
    apply le_iInf
    intro v
    obtain ⟨u, htu, huv⟩ := exists_between (show t < v.val from v.property)
    exact (iInf_le (fun u : Ioi t => rightPast u.val) ⟨u, htu⟩).trans
      (rightPast_le_past huv)
  · exact le_iInf fun u => rightPast_mono u.property.le

theorem projection_right_continuous (t : ℝ≥0) (f : JointL2) :
    ContinuousWithinAt (fun u => (rightPast u).starProjection f) (Ici t) t := by
  have hm : Monotone (fun u : OrderDual (Ioi t) => (rightPast u.val)ᗮ) := by
    intro u v huv
    exact Submodule.orthogonal_le (rightPast_mono huv)
  have hp := Submodule.starProjection_tendsto_closure_iSup (ι := OrderDual (Ioi t))
    (fun u : OrderDual (Ioi t) => (rightPast u.val)ᗮ) hm f
  have hc : Tendsto (fun _ : OrderDual (Ioi t) => f) atTop (𝓝 f) := tendsto_const_nhds
  have hs := hc.sub hp
  have he (u : OrderDual (Ioi t)) :
      f - (rightPast u.val)ᗮ.starProjection f = (rightPast u.val).starProjection f := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  have hk : (⨆ u : OrderDual (Ioi t), (rightPast u.val)ᗮ).topologicalClosureᗮ =
      rightPast t := by
    rw [Submodule.orthogonal_closure, ← Submodule.iInf_orthogonal]
    simp only [Submodule.orthogonal_orthogonal]
    exact rightPast_idempotent t
  have hl : f - (⨆ u : OrderDual (Ioi t), (rightPast u.val)ᗮ).topologicalClosure.starProjection f =
      (rightPast t).starProjection f := by
    simpa only [hk] using (Submodule.starProjection_orthogonal_val
      (K := (⨆ u : OrderDual (Ioi t), (rightPast u.val)ᗮ).topologicalClosure) f).symm
  have ht : Tendsto (fun u : Ioi t => (rightPast u.val).starProjection f) atBot
      (𝓝 ((rightPast t).starProjection f)) := by
    simpa only [he, hl] using! hs
  apply continuousWithinAt_Ioi_iff_Ici.mp
  exact (tendsto_comp_coe_Ioi_atBot (a := t)).mp ht

theorem rightLimitClass_right_continuous (t : ℝ≥0) :
    ContinuousWithinAt rightLimitClass (Ici t) t := by
  have hT : t < t + 1 := lt_add_of_pos_right _ (by norm_num)
  have hp := (projection_right_continuous t
    (IBMIntrinsicQuadraticMartingale.valueClass (t + 1) : JointL2)).mono Ioi_subset_Ici_self
  have he : rightLimitClass =ᶠ[𝓝[>] t]
      (fun u => (rightPast u).starProjection
        (IBMIntrinsicQuadraticMartingale.valueClass (t + 1) : JointL2)) := by
    filter_upwards [(eventually_lt_nhds hT).filter_mono inf_le_left] with u hu
    exact rightLimitClass_horizon hu
  apply continuousWithinAt_Ioi_iff_Ici.mp
  change Tendsto rightLimitClass (𝓝[>] t) (𝓝 (rightLimitClass t))
  have hr := Tendsto.congr' he.symm hp.tendsto
  simpa only [← rightLimitClass_horizon hT] using hr

end OperatorDerivativeRewrite.Foundation.IBMRightGermContinuity
