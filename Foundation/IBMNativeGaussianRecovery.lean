import Foundation.IBMIntrinsicDivergenceClosure
import Foundation.GaussianBochnerDivergenceRecovery
import Foundation.BochnerLiftAdjointInclusion

/-! Actual native Gaussian source recovery, retaining the two-factor mean remainder. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMNativeGaussianRecovery
open InfiniteGaussian IBMTimeAveragedObservable IBMFiniteAverageCore IBMIntrinsicOperators
open IBMJointIntrinsicDerivative GaussianBochnerDivergenceRecovery GaussianNumberSectors
set_option backward.isDefEq.respectTransparency false
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

def zeroSector : ScalarFieldSpace →L[ℝ] ScalarFieldSpace :=
  (projection 0).compLpL 2 gaussianProduct

theorem fiberCenter_eq (u : ScalarFieldSpace) : fiberCenter gaussianProduct u = u - zeroSector u := by
  apply Lp.ext
  filter_upwards [fiberCenter_coeFn gaussianProduct u, (projection 0).coeFn_compLpL u,
    Lp.coeFn_sub u (zeroSector u)] with ω hc hp hs
  rw [hc, hs]
  change u ω - projection 0 (u ω) = u ω - zeroSector u ω
  rw [show zeroSector u ω = projection 0 (u ω) from hp]

def clockVacuum (f : JointL2) : JointL2 := clockUnitary.symm (zeroSector (clockUnitary f))
def sourceVacuum (f : JointL2) : JointL2 := sourceUnitary.symm (zeroSector (sourceUnitary f))
def clockRecovery (f : JointL2) : FieldSpace := fiberRecovery gaussianProduct (clockUnitary f)
def sourceRecovery (f : JointL2) : FieldSpace := fiberRecovery gaussianProduct (sourceUnitary f)

theorem fiber_recovery_adjoint_graph (u : ScalarFieldSpace) :
    (fiberRecovery gaussianProduct u, fiberCenter gaussianProduct u) ∈ partialDerivative.adjoint.graph :=
  LinearPMap.le_graph_of_le
    (BochnerLiftAdjointInclusion.lift_adjoint_le gaussianProduct closedCylindricalDerivative
      closedCylindricalDerivative_dense_domain) (fiberRecovery_graph gaussianProduct u)

theorem clock_recovery_graph (f : JointL2) :
    (clockRecovery f, f-clockVacuum f) ∈ clockDerivative.adjoint.graph := by
  have hg := fiber_recovery_adjoint_graph (clockUnitary f)
  have hd := LinearPMap.mem_domain_of_mem_graph hg
  have hc : clockRecovery f ∈ clockDerivative.adjoint.domain := by
    rw [clock_adjoint_domain]
    exact hd
  refine clockDerivative.adjoint.mem_graph_iff.mpr ⟨⟨_, hc⟩, rfl, ?_⟩
  rw [clock_adjoint_apply _ hc hd]
  have hv := (partialDerivative.adjoint.image_iff hd).mpr hg
  change clockUnitary.symm (partialDerivative.adjoint
    ⟨fiberRecovery gaussianProduct (clockUnitary f), hd⟩) = f-clockVacuum f
  rw [hv.symm, fiberCenter_eq, map_sub, LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem source_recovery_graph (f : JointL2) :
    (sourceRecovery f, f-sourceVacuum f) ∈ sourceDerivative.adjoint.graph := by
  have hg := fiber_recovery_adjoint_graph (sourceUnitary f)
  have hd := LinearPMap.mem_domain_of_mem_graph hg
  have hc : sourceRecovery f ∈ sourceDerivative.adjoint.domain := by
    rw [source_adjoint_domain]
    exact hd
  refine sourceDerivative.adjoint.mem_graph_iff.mpr ⟨⟨_, hc⟩, rfl, ?_⟩
  rw [source_adjoint_apply _ hc hd]
  have hv := (partialDerivative.adjoint.image_iff hd).mpr hg
  change sourceUnitary.symm (partialDerivative.adjoint
    ⟨fiberRecovery gaussianProduct (sourceUnitary f), hd⟩) = f-sourceVacuum f
  rw [hv.symm, fiberCenter_eq, map_sub, LinearIsometryEquiv.symm_apply_apply]
  rfl

def recoveryPair (f : JointL2) : JointFieldSpace :=
  pairField (sourceRecovery (clockVacuum f)) (clockRecovery f)

theorem recovery_pair_graph (f : JointL2) :
    ∃ h : recoveryPair f ∈ jointDivergence.domain,
      jointDivergence ⟨recoveryPair f, h⟩ =
        IntrinsicSpace.orthogonalProjectionOnto (f-sourceVacuum (clockVacuum f)) := by
  have hs := source_recovery_graph (clockVacuum f)
  have hc := clock_recovery_graph f
  have hsd := LinearPMap.mem_domain_of_mem_graph hs
  have hcd := LinearPMap.mem_domain_of_mem_graph hc
  obtain ⟨h, hv⟩ := ambient_pair_divergence ⟨_, hsd⟩ ⟨_, hcd⟩
  change jointDivergence ⟨recoveryPair f, h⟩ = _ at hv
  refine ⟨h, ?_⟩
  change jointDivergence ⟨recoveryPair f, h⟩ = _
  rw [hv]
  have hsv := (sourceDerivative.adjoint.image_iff hsd).mpr hs
  have hcv := (clockDerivative.adjoint.image_iff hcd).mpr hc
  rw [hsv.symm, hcv.symm]
  congr 1
  abel

end OperatorDerivativeRewrite.Foundation.IBMNativeGaussianRecovery
