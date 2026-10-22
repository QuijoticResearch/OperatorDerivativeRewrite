import Foundation.IBMIntrinsicDivergenceClosure
import Foundation.GaussianBochnerDivergenceRecovery
import Foundation.BochnerLiftAdjointInclusion

/-! Bounded explicit recovery in the ACTUAL native source adjoints, followed
by the genuine intrinsic conditional divergence. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeSourceRecovery
open InfiniteGaussian IBMTimeAveragedObservable IBMFiniteAverageCore IBMIntrinsicOperators
open GaussianBochnerDivergenceRecovery
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

def sourceRecovery : JointL2 →L[ℝ] FieldSpace :=
  (fiberRecovery gaussianProduct).comp sourceUnitary.toLinearIsometry.toContinuousLinearMap

def clockRecovery : JointL2 →L[ℝ] FieldSpace :=
  (fiberRecovery gaussianProduct).comp clockUnitary.toLinearIsometry.toContinuousLinearMap

def sourceCenter (f : JointL2) : JointL2 :=
  sourceUnitary.symm (fiberCenter gaussianProduct (sourceUnitary f))

def clockCenter (f : JointL2) : JointL2 :=
  clockUnitary.symm (fiberCenter gaussianProduct (clockUnitary f))

def sourceVacuum (f : JointL2) : JointL2 :=
  sourceUnitary.symm ((GaussianNumberSectors.projection 0).compLpL 2 gaussianProduct
    (sourceUnitary f))

def clockVacuum (f : JointL2) : JointL2 :=
  clockUnitary.symm ((GaussianNumberSectors.projection 0).compLpL 2 gaussianProduct
    (clockUnitary f))

theorem fiber_center_split (f : ScalarFieldSpace) :
    fiberCenter gaussianProduct f =
      f - (GaussianNumberSectors.projection 0).compLpL 2 gaussianProduct f := by
  apply Lp.ext
  filter_upwards [fiberCenter_coeFn gaussianProduct f,
    (GaussianNumberSectors.projection 0).coeFn_compLpL f,
    Lp.coeFn_sub f ((GaussianNumberSectors.projection 0).compLpL 2 gaussianProduct f)]
    with x hc hp hs
  rw [hc, hs, Pi.sub_apply, hp]

theorem source_center_split (f : JointL2) : sourceCenter f = f - sourceVacuum f := by
  simp only [sourceCenter, sourceVacuum, fiber_center_split, map_sub,
    sourceUnitary.symm_apply_apply]

theorem clock_center_split (f : JointL2) : clockCenter f = f - clockVacuum f := by
  simp only [clockCenter, clockVacuum, fiber_center_split, map_sub,
    clockUnitary.symm_apply_apply]

theorem fiber_recovery_native_graph (f : ScalarFieldSpace) :
    (fiberRecovery gaussianProduct f, fiberCenter gaussianProduct f) ∈
      partialDerivative.adjoint.graph :=
  LinearPMap.le_graph_of_le
    (BochnerLiftAdjointInclusion.lift_adjoint_le gaussianProduct
      closedCylindricalDerivative closedCylindricalDerivative_dense_domain)
    (fiberRecovery_graph gaussianProduct f)

theorem source_recovery_graph (f : JointL2) :
    (sourceRecovery f, sourceCenter f) ∈ sourceDerivative.adjoint.graph := by
  have hg := fiber_recovery_native_graph (sourceUnitary f)
  have hm := LinearPMap.mem_domain_of_mem_graph hg
  have hs : sourceRecovery f ∈ sourceDerivative.adjoint.domain := by
    rw [source_adjoint_domain]
    exact hm
  apply sourceDerivative.adjoint.mem_graph_iff.mpr
  refine ⟨⟨_, hs⟩, rfl, ?_⟩
  rw [source_adjoint_apply _ hs hm]
  exact congrArg sourceUnitary.symm ((partialDerivative.adjoint.image_iff hm).mpr hg).symm

theorem clock_recovery_graph (f : JointL2) :
    (clockRecovery f, clockCenter f) ∈ clockDerivative.adjoint.graph := by
  have hg := fiber_recovery_native_graph (clockUnitary f)
  have hm := LinearPMap.mem_domain_of_mem_graph hg
  have hs : clockRecovery f ∈ clockDerivative.adjoint.domain := by
    rw [clock_adjoint_domain]
    exact hm
  apply clockDerivative.adjoint.mem_graph_iff.mpr
  refine ⟨⟨_, hs⟩, rfl, ?_⟩
  rw [clock_adjoint_apply _ hs hm]
  exact congrArg clockUnitary.symm ((partialDerivative.adjoint.image_iff hm).mpr hg).symm

theorem source_recovery_norm (f : JointL2) : ‖sourceRecovery f‖ ≤ ‖f‖ :=
  (fiberRecovery_norm_le gaussianProduct (sourceUnitary f)).trans_eq (sourceUnitary.norm_map f)

theorem clock_recovery_norm (f : JointL2) : ‖clockRecovery f‖ ≤ ‖f‖ :=
  (fiberRecovery_norm_le gaussianProduct (clockUnitary f)).trans_eq (clockUnitary.norm_map f)

theorem intrinsic_source_recovery (f : JointL2) :
    ∃ h : sourceRecovery f ∈ intrinsicSource.adjoint.domain,
      intrinsicSource.adjoint ⟨sourceRecovery f, h⟩ =
        IntrinsicSpace.orthogonalProjectionOnto (sourceCenter f) := by
  let u : sourceDerivative.adjoint.domain :=
    ⟨sourceRecovery f, LinearPMap.mem_domain_of_mem_graph (source_recovery_graph f)⟩
  refine ⟨source_source_divergence_mem u, ?_⟩
  rw [intrinsic_source_divergence_value u]
  exact congrArg IntrinsicSpace.orthogonalProjectionOnto
    ((sourceDerivative.adjoint.image_iff u.property).mpr (source_recovery_graph f)).symm

theorem intrinsic_clock_recovery (f : JointL2) :
    ∃ h : clockRecovery f ∈ intrinsicClock.adjoint.domain,
      intrinsicClock.adjoint ⟨clockRecovery f, h⟩ =
        IntrinsicSpace.orthogonalProjectionOnto (clockCenter f) := by
  let u : clockDerivative.adjoint.domain :=
    ⟨clockRecovery f, LinearPMap.mem_domain_of_mem_graph (clock_recovery_graph f)⟩
  refine ⟨clock_source_divergence_mem u, ?_⟩
  rw [intrinsic_clock_divergence_value u]
  exact congrArg IntrinsicSpace.orthogonalProjectionOnto
    ((clockDerivative.adjoint.image_iff u.property).mpr (clock_recovery_graph f)).symm

set_option maxHeartbeats 800000 in
-- The actual native pair-divergence domains require a larger local budget.
/-- An explicit actual native pair reconstructs the input modulo the ACTUAL
composed factor-zero projection. Global-mean identification is separate. -/
theorem ordered_intrinsic_reconstruction (f : JointL2) :
    ∃ h : IBMJointIntrinsicDerivative.pairField
        (sourceRecovery f) (clockRecovery (sourceVacuum f)) ∈
        IBMJointIntrinsicDerivative.jointDivergence.domain,
      IBMJointIntrinsicDerivative.jointDivergence ⟨_, h⟩ =
        IntrinsicSpace.orthogonalProjectionOnto (f - clockVacuum (sourceVacuum f)) := by
  let a : sourceDerivative.adjoint.domain :=
    ⟨sourceRecovery f, LinearPMap.mem_domain_of_mem_graph (source_recovery_graph f)⟩
  let b : clockDerivative.adjoint.domain :=
    ⟨clockRecovery (sourceVacuum f),
      LinearPMap.mem_domain_of_mem_graph (clock_recovery_graph (sourceVacuum f))⟩
  obtain ⟨h, hv⟩ := IBMJointIntrinsicDerivative.ambient_pair_divergence a b
  have ha : sourceDerivative.adjoint a = sourceCenter f :=
    ((sourceDerivative.adjoint.image_iff a.property).mpr (source_recovery_graph f)).symm
  have hb : clockDerivative.adjoint b = clockCenter (sourceVacuum f) :=
    ((clockDerivative.adjoint.image_iff b.property).mpr
      (clock_recovery_graph (sourceVacuum f))).symm
  have hs : sourceDerivative.adjoint a + clockDerivative.adjoint b =
      f - clockVacuum (sourceVacuum f) := by
    rw [ha, hb, source_center_split, clock_center_split]
    abel
  exact ⟨h, hv.trans (congrArg IntrinsicSpace.orthogonalProjectionOnto hs)⟩

end OperatorDerivativeRewrite.Foundation.IBMNativeSourceRecovery
