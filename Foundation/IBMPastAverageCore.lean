import Foundation.IBMNaturalFiltrationObstruction
import Foundation.IBMFiniteAverageCore

/-! Past-localized actual IBM averages and endpoint recovery. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPastAverageCore
open InfiniteGaussian IBMTimeAveragedObservable IBMNaturalFiltrationObstruction
open IBMFiniteAverageCore IBMClockOverlapEnergy
set_option backward.isDefEq.respectTransparency false
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

theorem point_mem_past {s T : ℝ≥0} (hs : s ≤ T) :
    (intrinsicCurve s : JointL2) ∈ past T := by
  change AEStronglyMeasurable[naturalFiltration T]
    (intrinsicCurve s : JointL2) IBMSourceLaws.jointMeasure
  exact ((point_stronglyAdapted s).mono (naturalFiltration.mono hs)).aestronglyMeasurable.congr
    (joint_point_actual_ae s).symm

/-- This uses the actual closed natural-past subspace, not a source-chaos projection. -/
theorem nativeAverage_mem_past {r : ℝ} {T : ℝ≥0} (hr : r ≤ T) :
    nativeAverage r ∈ past T := by
  let : CompleteSpace (past T) := (past_closed T).completeSpace_coe
  have hi : Integrable (fun t : ℝ => (intrinsicCurve t.toNNReal : JointL2)) (window r) :=
    IntrinsicSpace.subtypeL.integrable_comp (intrinsicCurve_integrable r)
  have he : nativeAverage r = ∫ t, (intrinsicCurve t.toNNReal : JointL2) ∂window r := by
    rw [nativeAverage_eq_intrinsicAverage]
    exact (IntrinsicSpace.subtypeL.integral_comp_comm (intrinsicCurve_integrable r)).symm
  have hp : ∀ᵐ t ∂window r,
      (past T).starProjection (intrinsicCurve t.toNNReal : JointL2) =
        (intrinsicCurve t.toNNReal : JointL2) := by
    apply (ae_restrict_mem measurableSet_Ioc).mono
    intro t ht
    apply Submodule.starProjection_eq_self_iff.mpr
    exact point_mem_past (by exact_mod_cast (Real.toNNReal_le_iff_le_coe.mpr (ht.2.trans hr)))
  have hfix : (past T).starProjection (nativeAverage r) = nativeAverage r := by
    rw [he, ← (past T).starProjection.integral_comp_comm hi]
    exact integral_congr_ae hp
  exact Submodule.starProjection_eq_self_iff.mp hfix

def pastCore (T : ℝ≥0) : Submodule ℝ JointL2 := intrinsicCore ⊓ past T

theorem closure_le_past (T : ℝ≥0) : (pastCore T).topologicalClosure ≤ past T :=
  (pastCore T).topologicalClosure_minimal inf_le_right (past_closed T)

theorem pastCore_mono {S T : ℝ≥0} (h : S ≤ T) : pastCore S ≤ pastCore T := by
  intro f hf
  exact ⟨hf.1, (show AEStronglyMeasurable[naturalFiltration S]
    f IBMSourceLaws.jointMeasure from hf.2).mono (naturalFiltration.mono h)⟩

theorem bounded_chain_past (T : ℝ≥0) (f : JointL2) (hf : f ∈ pastCore T)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : JointL2, F ∈ pastCore T ∧
      F =ᵐ[IBMSourceLaws.jointMeasure] fun ω => φ (f ω) := by
  obtain ⟨F, hF, ha⟩ := bounded_chain f hf.1 φ dφ hd hc A B hA hB
  refine ⟨F, ⟨hF, ?_⟩, ha⟩
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  exact (hφ.comp_aestronglyMeasurable (show AEStronglyMeasurable[naturalFiltration T]
    f IBMSourceLaws.jointMeasure from hf.2)).congr ha.symm

theorem average_mem_core {r : ℝ} {T : ℝ≥0} (h0 : 0 ≤ r) (hT : r ≤ T) :
    nativeAverage r ∈ pastCore T :=
  ⟨nativeAverage_mem r h0, nativeAverage_mem_past hT⟩

/-- Left increments recover the endpoint without sampling any future IBM value.
Only L2 closure is asserted; no pointwise Malliavin domain membership follows. -/
theorem point_mem_past_core_closure {t : ℝ} {T : ℝ≥0} (ht : 0 < t) (hT : t ≤ T) :
    jointRealization (IBMRandomTimeHilbert.randomSourceL2 t.toNNReal) ∈
      (pastCore T).topologicalClosure := by
  apply (pastCore T).isClosed_topologicalClosure.mem_of_tendsto
    (nativeAverage_hasDerivAt ht).tendsto_slope_zero_left
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (neg_neg_of_pos ht)).filter_mono nhdsWithin_le_nhds] with e he he0
  apply (pastCore T).le_topologicalClosure
  exact (pastCore T).smul_mem _ ((pastCore T).sub_mem
    (average_mem_core (by linarith) (by linarith [show e < 0 from he]))
    (average_mem_core ht.le hT))

end OperatorDerivativeRewrite.Foundation.IBMPastAverageCore
