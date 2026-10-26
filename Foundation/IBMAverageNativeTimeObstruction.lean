import Foundation.IBMAverageTimeGraph
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! The actual averaged IBM has a native derivative, but that native derivative
has no strong ordinary-time derivative at any positive time. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMAverageNativeTimeObstruction
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMRampSimpsonNativeAverage
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

theorem actual_average_hasDerivAt {T : ℝ} (hT : 0 < T) :
    HasDerivAt (fun t : ℝ => intrinsicAverage (t.toNNReal:ℝ)) (intrinsicCurve T.toNNReal) T := by
  have hc := intrinsicCurve_continuous.comp continuous_real_toNNReal
  have h := (hc.integral_hasStrictDerivAt (0:ℝ) T).hasDerivAt
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hT] with t ht
  rw [Real.coe_toNNReal _ ht.le,intervalIntegral.integral_of_le ht.le]
  rfl

theorem nativeGradient_no_hasDerivAt {T : ℝ} (hT : 0 < T) (g : JointFieldSpace) :
    ¬ HasDerivAt (fun t : ℝ => averageGradient t.toNNReal) g T := by
  intro hg
  have hd := (actual_average_hasDerivAt hT).prodMk hg
  have hm (t : ℝ) : (intrinsicAverage (t.toNNReal:ℝ),averageGradient t.toNNReal) ∈
      jointDerivative.graph :=
    jointDerivative.mem_graph ⟨_,average_mem_joint_domain t.toNNReal⟩
  have hs : ∀ᶠ e : ℝ in 𝓝[>] 0,
      e⁻¹ • ((intrinsicAverage ((T+e).toNNReal:ℝ),averageGradient (T+e).toNNReal) -
        (intrinsicAverage (T.toNNReal:ℝ),averageGradient T.toNNReal)) ∈ jointDerivative.graph :=
    Eventually.of_forall fun e => jointDerivative.graph.smul_mem e⁻¹
      (jointDerivative.graph.sub_mem (hm (T+e)) (hm T))
  have hx := jointDerivative_closed.mem_of_tendsto hd.tendsto_slope_zero_right hs
  exact IBMPointClockDomainObstruction.actual_point_not_joint_domain T.toNNReal
    (Real.toNNReal_pos.mpr hT) (LinearPMap.mem_domain_of_mem_graph hx)

theorem nativeGradient_not_differentiableAt {T : ℝ} (hT : 0 < T) :
    ¬ DifferentiableAt ℝ (fun t : ℝ => averageGradient t.toNNReal) T := by
  intro h
  exact nativeGradient_no_hasDerivAt hT _ h.hasDerivAt

/-- Every positive vanishing step sequence gives native time-slope norm escape.
This is about time increments of the native AVERAGE derivative, not the earlier
integrals of point regularizer gradients. -/
theorem native_time_slope_norm_escape {T : ℝ} (hT : 0 < T) (e : ℕ → ℝ)
    (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ‖(e n)⁻¹ •
      (averageGradient (T+e n).toNNReal-averageGradient T.toNNReal)‖) atTop atTop := by
  have hm (t : ℝ) : (intrinsicAverage (t.toNNReal:ℝ),averageGradient t.toNNReal) ∈
      jointDerivative.graph :=
    jointDerivative.mem_graph ⟨_,average_mem_joint_domain t.toNNReal⟩
  have hs := (actual_average_hasDerivAt hT).tendsto_slope_zero_right.comp
    (tendsto_nhdsWithin_iff.mpr ⟨he0,Eventually.of_forall he⟩)
  exact ClosedOperatorEscapeEnergy.output_norm_tendsto_atTop jointDerivative
    jointDerivative_closed jointDerivative_dense
    (fun n => jointDerivative.graph.smul_mem (e n)⁻¹
      (jointDerivative.graph.sub_mem (hm (T+e n)) (hm T))) hs
    (IBMPointClockDomainObstruction.actual_point_not_joint_domain T.toNNReal
      (Real.toNNReal_pos.mpr hT))

end OperatorDerivativeRewrite.Foundation.IBMAverageNativeTimeObstruction
