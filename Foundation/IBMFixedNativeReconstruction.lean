import Foundation.IBMFixedStochasticFamily
import Foundation.IBMIntrinsicGraphDual
import Foundation.IBMObservedInitialGerm

/-! Fixed stochastic channels reconstruct every intrinsic remainder, with
coefficients tested by the ORIGINAL native divergence and graph-dual derivative. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFixedNativeReconstruction
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicGraphDual
open IBMFixedStochasticFamily IBMStochasticNativeDivergence
open IBMObservedTerminalMartingale IBMFullPredictableIntegral
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] IBMJointIntrinsicDerivative.jointDerivative

def nativeTest (i : basisSet) : jointDivergence.domain :=
  ⟨nativeField (terminal i : JointL2) (integrand i), nativeField_mem _ _⟩

theorem nativeTest_value (i : basisSet) : jointDivergence (nativeTest i) = terminal i := by
  apply Subtype.ext
  exact (congrArg (fun z : IntrinsicSpace => (z : JointL2))
    (native_divergence (terminal i : JointL2) (integrand i))).trans (integral_integrand i)

theorem nativeTest_norm (i : basisSet) : ‖(nativeTest i : JointFieldSpace)‖^2 ≤ 2 := by
  change ‖nativeField (terminal i : JointL2) (integrand i)‖^2 ≤ 2
  simpa only [integrand_norm, one_pow, mul_one] using nativeField_bound (terminal i : JointL2) (integrand i)

theorem coefficient_generalized (f : IntrinsicSpace) (i : basisSet) :
    coefficient f i = weakDerivative f (testOf (nativeTest i)) := by
  calc
    _ = inner ℝ (terminal i : JointL2) (f : JointL2) := coefficient_pairing f i
    _ = inner ℝ f (terminal i) := real_inner_comm _ _
    _ = inner ℝ f (jointDivergence (nativeTest i)) :=
      congrArg (fun z : IntrinsicSpace => inner ℝ f z) (nativeTest_value i).symm
    _ = _ := rfl

theorem coefficient_native (f : jointDerivative.domain) (i : basisSet) :
    coefficient (f : IntrinsicSpace) i = inner ℝ (nativeTest i : JointFieldSpace) (jointDerivative f) := by
  have he : inner ℝ (terminal i) (f : IntrinsicSpace) =
      inner ℝ (jointDivergence (nativeTest i)) (f : IntrinsicSpace) :=
    congrArg (fun z : IntrinsicSpace => inner ℝ z (f : IntrinsicSpace)) (nativeTest_value i).symm
  exact (coefficient_pairing (f : IntrinsicSpace) i).trans
    (he.trans (jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense (nativeTest i) f))

theorem generalized_stochastic_reconstruction (f : IntrinsicSpace) :
    HasSum (fun i : basisSet => integral (terminal i : JointL2)
      (weakDerivative f (testOf (nativeTest i)) • integrand i))
      ((f : JointL2)-channelClass (f : JointL2) 0) := by
  simpa only [coefficient_generalized] using stochastic_reconstruction f

theorem native_stochastic_reconstruction (f : jointDerivative.domain) :
    HasSum (fun i : basisSet => integral (terminal i : JointL2)
      (inner ℝ (nativeTest i : JointFieldSpace) (jointDerivative f) • integrand i))
      (((f : IntrinsicSpace) : JointL2)-channelClass ((f : IntrinsicSpace) : JointL2) 0) := by
  simpa only [coefficient_native] using stochastic_reconstruction (f : IntrinsicSpace)

theorem generalized_energy (f : IntrinsicSpace) :
    HasSum (fun i : basisSet => (weakDerivative f (testOf (nativeTest i)))^2) (‖remainder f‖^2) := by
  simpa only [coefficient_generalized] using coefficient_energy f

theorem observed_reconstruction (t : ℝ≥0) :
    HasSum (fun i : basisSet => integral (terminal i : JointL2)
      (weakDerivative (intrinsicCurve t) (testOf (nativeTest i)) • integrand i))
      (intrinsicCurve t : JointL2) := by
  have hz : channelClass (intrinsicCurve t : JointL2) 0 = 0 :=
    IBMObservedInitialGerm.initial_channel_zero t
  simpa only [hz, sub_zero] using generalized_stochastic_reconstruction (intrinsicCurve t)

theorem observed_one_nonzero_coefficient :
    ∃ i : basisSet, weakDerivative (intrinsicCurve 1) (testOf (nativeTest i)) ≠ 0 := by
  by_contra! h
  have hz : ∀ i : basisSet, coefficient (intrinsicCurve 1) i = 0 := by
    intro i
    exact (coefficient_generalized _ i).trans (h i)
  have hm := (coefficients_zero_iff _).mp hz
  have hp : channelClass (intrinsicCurve 1 : JointL2) 0 = (intrinsicCurve 1 : JointL2) :=
    Submodule.starProjection_eq_self_iff.mpr hm
  have he : (intrinsicCurve 1 : JointL2) = 0 :=
    hp.symm.trans (IBMObservedInitialGerm.initial_channel_zero 1)
  exact IBMDeterministicRangeObstruction.observed_one_ne_zero he

end OperatorDerivativeRewrite.Foundation.IBMFixedNativeReconstruction
