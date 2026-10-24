import Foundation.IBMSceneryNativeAdjoint
import Foundation.IBMNativeClockDirection

/-! Explicit source and adapted-clock channels reconstruct the ACTUAL IBM
terminal observable through the ORIGINAL intrinsic joint divergence. The
scenery parameter is not an observed-filtration martingale representation. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedJointReconstruction
open InfiniteGaussian GaussianTimeHilbert IBMTimeAveragedObservable
open IBMIntrinsicOperators IBMJointIntrinsicDerivative IBMFiniteAverageCore
open IBMSpatialTerminalReconstruction IBMPhysicalNoiseRealization
open IBMNativeDeterministicFields
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

def sourceField (T : ℝ≥0) : FieldSpace :=
  directionField (physicalToCoefficient (initialKernel T))

theorem source_mem (T : ℝ≥0) : sourceField T ∈ sourceDerivative.adjoint.domain := by
  rw [source_adjoint_domain]
  exact direction_partial_mem _

theorem initial_source_curry (T : ℝ≥0) :
    sourceUnitary (initialValue T) =
      BochnerClosedOperator.tensor gaussianProduct gaussianOne
        (physicalNoise (initialKernel T)) := by
  change ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
    (ProductL2Curry.swap gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct
        ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
          (IBMClockPhysicalOccupation.noiseLift
            (Lp.const 2 gaussianProduct (initialKernel T)))))) = _
  have he := IBMNonlinearAverageGraph.swap_swap
    ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
      (IBMClockPhysicalOccupation.noiseLift (Lp.const 2 gaussianProduct (initialKernel T))))
  refine ((congrArg (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct) he).trans
    (LinearIsometryEquiv.apply_symm_apply _ _)).trans ?_
  apply Lp.ext
  filter_upwards [BochnerLinearIsometry.lift_coeFn gaussianProduct physicalNoise
    (Lp.const 2 gaussianProduct (initialKernel T)),
    Lp.coeFn_const 2 gaussianProduct (initialKernel T),
    BochnerClosedOperator.tensor_coeFn gaussianProduct gaussianOne
      (physicalNoise (initialKernel T)), gaussianOne_coeFn] with Y hn hc ht ho
  change IBMClockPhysicalOccupation.noiseLift _ Y = _ at hn
  rw [hn, hc, ht, ho, one_smul]
  rfl

theorem source_value (T : ℝ≥0) :
    sourceDerivative.adjoint ⟨sourceField T, source_mem T⟩ = initialValue T := by
  have hp : sourceField T ∈ partialDerivative.adjoint.domain := direction_partial_mem _
  have hv : partialDerivative.adjoint ⟨sourceField T,hp⟩ =
      BochnerClosedOperator.tensor gaussianProduct gaussianOne
        (physicalNoise (initialKernel T)) :=
    IBMNativeClockDirection.partial_value (physicalToCoefficient (initialKernel T))
  calc
    _ = sourceUnitary.symm (partialDerivative.adjoint ⟨sourceField T,hp⟩) :=
      source_adjoint_apply _ (source_mem T) hp
    _ = sourceUnitary.symm (sourceUnitary (initialValue T)) :=
      congrArg sourceUnitary.symm (hv.trans (initial_source_curry T).symm)
    _ = _ := sourceUnitary.symm_apply_apply _

def clockField (T : ℝ≥0) : FieldSpace :=
  IBMSceneryNativeAdjoint.field T (IBMFoldedHeatNativeIto.scalarInput T)

theorem clock_mem (T : ℝ≥0) : clockField T ∈ clockDerivative.adjoint.domain :=
  IBMSceneryNativeAdjoint.clock_mem T _

theorem ambient_sum (T : ℝ≥0) (hT : 0 < T) :
    sourceDerivative.adjoint ⟨sourceField T, source_mem T⟩ +
      clockDerivative.adjoint ⟨clockField T, clock_mem T⟩ =
        (intrinsicCurve T : JointL2) := by
  have hc : clockDerivative.adjoint ⟨clockField T, clock_mem T⟩ =
      IBMFoldedHeatNativeIto.value T := IBMSceneryNativeAdjoint.clock_value T _
  rw [source_value, hc]
  rw [IBMFoldedCanonicalIdentification.native_value_eq_canonical T hT, add_comm,
    canonical_identity]
  apply Lp.ext
  exact (IBMSpatialPointClockObstruction.source_actual T).trans
    (joint_point_actual_ae T).symm

def integrand (T : ℝ≥0) : JointFieldSpace := pairField (sourceField T) (clockField T)

theorem reconstruction (T : ℝ≥0) (hT : 0 < T) :
    ∃ hi : integrand T ∈ jointDivergence.domain,
      jointDivergence ⟨integrand T, hi⟩ = intrinsicCurve T := by
  obtain ⟨hi,hv⟩ := ambient_pair_divergence
    ⟨sourceField T, source_mem T⟩ ⟨clockField T, clock_mem T⟩
  refine ⟨hi, hv.trans ?_⟩
  rw [ambient_sum T hT]
  exact IntrinsicSpace.orthogonalProjectionOnto_mem_subspace_eq_self (intrinsicCurve T)

theorem terminal_duality (T : ℝ≥0) (hT : 0 < T) (F : jointDerivative.domain) :
    inner ℝ (intrinsicCurve T) (F : IntrinsicSpace) =
      inner ℝ (integrand T) (jointDerivative F) := by
  obtain ⟨hi,hv⟩ := reconstruction T hT
  have h := jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense
    ⟨integrand T,hi⟩ F
  rw [hv] at h
  exact h

end OperatorDerivativeRewrite.Foundation.IBMFoldedJointReconstruction
