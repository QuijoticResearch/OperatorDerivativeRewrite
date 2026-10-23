import Foundation.IBMMultichannelCompletion
import Foundation.IBMIntrinsicGraphDual

/-! Actual completed stochastic integration, original native divergence and graph-dual reconstruction. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompletedNativeCalculus
open IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMMultichannelCompletion IBMNativeGaussianRecovery IBMStochasticNativeDivergence
open IBMIntrinsicRightGerm IBMPredictableIntegralObservable
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local instance] componentAdd componentGroup componentModule componentZeroDec
attribute [local irreducible] IBMJointIntrinsicDerivative.jointDerivative
local instance : DecidableEq IBMFixedStochasticFamily.basisSet := Classical.decEq _
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
variable {ι : Type*} [DecidableEq ι] (F : ι → JointL2)

def observable (z : Completed F) : IntrinsicSpace :=
  ⟨completedIntegral F z, (completed_mem_remainder F z).1⟩

def transfer : Completed F →L[ℝ] JointFieldSpace :=
  IBMNativePredictableTransfer.recoveryOperator.comp (completedIntegral F).toContinuousLinearMap

theorem observable_centered (z : Completed F) : inner ℝ jointOne (observable F z : JointL2) = 0 := by
  rw [real_inner_comm]
  exact (Submodule.mem_orthogonal' _ _).mp (completed_mem_remainder F z).2 _
    (IBMIntrinsicRightGerm.past_le_rightPast 0 (jointOne_mem_past 0))

theorem transfer_mem (z : Completed F) : transfer F z ∈ jointDivergence.domain :=
  (centered_observable_recovery (observable F z) (observable_centered F z)).choose

theorem transfer_divergence (z : Completed F) :
    jointDivergence ⟨transfer F z, transfer_mem F z⟩ = observable F z :=
  (centered_observable_recovery (observable F z) (observable_centered F z)).choose_spec

theorem transfer_bound (z : Completed F) : ‖transfer F z‖^2 ≤ 2*‖z‖^2 := by
  change ‖recoveryPair (completedIntegral F z)‖^2 ≤ _
  simpa only [(completedIntegral F).norm_map] using recovery_bound (completedIntegral F z)

theorem transfer_single (i : ι) (H : IBMPredictableLpDictionary.PredictableL2 (F i)) :
    transfer F (IBMMultichannelCompletion.embed F
      (DirectSum.lof ℝ ι (fun i => IBMPredictableLpDictionary.PredictableL2 (F i)) i H)) =
        IBMNativePredictableTransfer.transfer (F i) H := by
  change IBMNativePredictableTransfer.recoveryOperator (completedIntegral F _) =
    IBMNativePredictableTransfer.recoveryOperator (IBMFullPredictableIntegral.integral (F i) H)
  exact congrArg IBMNativePredictableTransfer.recoveryOperator
    ((completedIntegral_embed F _).trans (rawIntegral_single F i H))

theorem integration_by_parts (z : Completed F) (f : jointDerivative.domain) :
    inner ℝ (observable F z) (f : IntrinsicSpace) = inner ℝ (transfer F z) (jointDerivative f) := by
  rw [← transfer_divergence F z]
  exact jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense _ f

theorem native_adjoint (f : jointDerivative.domain) :
    (transfer F).adjoint (jointDerivative f) =
      (completedIntegral F).toContinuousLinearMap.adjoint ((f : IntrinsicSpace) : JointL2) := by
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  exact (integration_by_parts F z f).symm

theorem fixed_adjoint (f : IntrinsicSpace) :
    (completedIntegral fixedFamily).toContinuousLinearMap.adjoint (f : JointL2) =
      fixedHilbertEquiv.symm (IBMFixedStochasticFamily.remainder f) := by
  apply ext_inner_left ℝ
  intro z
  have ho : inner ℝ (completedIntegral fixedFamily z)
      (IBMObservedTerminalMartingale.channelClass (f : JointL2) 0) = 0 :=
    (Submodule.mem_orthogonal' _ _).mp (completed_mem_remainder fixedFamily z).2 _
      ((rightPast 0).starProjection_apply_mem _)
  rw [ContinuousLinearMap.adjoint_inner_right]
  calc
    _ = inner ℝ (completedIntegral fixedFamily z) ((f : JointL2)-
        IBMObservedTerminalMartingale.channelClass (f : JointL2) 0) := by
      rw [inner_sub_right, ho, sub_zero]
      rfl
    _ = _ := by rw [← fixed_reconstruction f, (completedIntegral fixedFamily).inner_map_map]

theorem fixed_native_reconstruction (f : jointDerivative.domain) :
    completedIntegral fixedFamily ((transfer fixedFamily).adjoint (jointDerivative f)) =
      ((f : IntrinsicSpace) : JointL2)-IBMObservedTerminalMartingale.channelClass ((f : IntrinsicSpace) : JointL2) 0 := by
  rw [native_adjoint, fixed_adjoint, fixed_reconstruction]

def nativeTest (z : Completed F) : jointDivergence.domain := ⟨transfer F z, transfer_mem F z⟩

theorem weak_pairing (f : IntrinsicSpace) (z : Completed F) :
    IBMIntrinsicGraphDual.weakDerivative f (IBMIntrinsicGraphDual.testOf (nativeTest F z)) =
      inner ℝ f (observable F z) := by
  rw [IBMIntrinsicGraphDual.test_pairing]
  exact congrArg (fun g : IntrinsicSpace => inner ℝ f g) (transfer_divergence F z)

theorem weak_integrand_pairing (f : IntrinsicSpace) (z : Completed F) :
    inner ℝ z ((completedIntegral F).toContinuousLinearMap.adjoint (f : JointL2)) =
      IBMIntrinsicGraphDual.weakDerivative f (IBMIntrinsicGraphDual.testOf (nativeTest F z)) := by
  calc
    _ = inner ℝ ((completedIntegral F).toContinuousLinearMap z) (f : JointL2) :=
      (completedIntegral F).toContinuousLinearMap.adjoint_inner_right z (f : JointL2)
    _ = inner ℝ f (observable F z) := by
      change inner ℝ (completedIntegral F z) (f : JointL2) =
        inner ℝ (f : JointL2) (completedIntegral F z)
      exact real_inner_comm _ _
    _ = _ := (weak_pairing F f z).symm

theorem fixed_weak_reconstruction (f : IntrinsicSpace) :
    completedIntegral fixedFamily ((completedIntegral fixedFamily).toContinuousLinearMap.adjoint (f : JointL2)) =
      (f : JointL2)-IBMObservedTerminalMartingale.channelClass (f : JointL2) 0 := by
  rw [fixed_adjoint, fixed_reconstruction]

theorem weak_integrand_unique (f : IntrinsicSpace) :
    ∃! h : Completed F, ∀ z : Completed F, inner ℝ z h =
      IBMIntrinsicGraphDual.weakDerivative f (IBMIntrinsicGraphDual.testOf (nativeTest F z)) := by
  refine ⟨(completedIntegral F).toContinuousLinearMap.adjoint (f : JointL2),
    fun z => weak_integrand_pairing F f z, ?_⟩
  intro h hh
  apply ext_inner_left ℝ
  intro z
  exact (hh z).trans (weak_integrand_pairing F f z).symm

theorem fixed_integrand_norm (f : IntrinsicSpace) :
    ‖(completedIntegral fixedFamily).toContinuousLinearMap.adjoint (f : JointL2)‖ =
      ‖IBMFixedStochasticFamily.remainder f‖ := by
  rw [fixed_adjoint]
  exact fixedHilbertEquiv.symm.norm_map _

theorem fixed_native_integrand_energy (f : jointDerivative.domain) :
    ‖(transfer fixedFamily).adjoint (jointDerivative f)‖^2 =
      ‖IBMFixedStochasticFamily.remainder (f : IntrinsicSpace)‖^2 := by
  rw [native_adjoint, fixed_integrand_norm]

end OperatorDerivativeRewrite.Foundation.IBMCompletedNativeCalculus
