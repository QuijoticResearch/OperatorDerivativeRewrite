import Foundation.IBMJointRandomDistribution
import Foundation.IBMMixedClockLimit

/-! Actual IBM quadratic observations admit a sourcewise clock-L1 native
reconstruction. No membership in the smooth joint Banach test space is assumed,
and the source contraction is not identified with a projected intrinsic path. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMActualQuadraticRandomReconstruction
open InfiniteGaussian IBMTimeAveragedObservable IBMRawGridMixedObservable
open IBMMixedClockLimit GaussianTimeProcess IBMClippedClockCrossing

local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

def endpoint (H R S : ℝ≥0) : Lp ℝ 1 gaussianProduct :=
  (mixed_endpoint_integrable H R S).toL1 _

theorem endpoint_actual (H R S : ℝ≥0) :
    endpoint H R S =ᵐ[gaussianProduct] fun Y =>
      cap (process R Y) (process H Y)*cap (process S Y) (process H Y) :=
  (mixed_endpoint_integrable H R S).coeFn_toL1

def reconstruction (H R S : ℝ≥0) : Lp ℝ 1 gaussianProduct :=
  endpoint H R S-mixedOccupationClass H R S

theorem reconstruction_actual (H R S : ℝ≥0) :
    reconstruction H R S =ᵐ[gaussianProduct] fun Y =>
      cap (process R Y) (process H Y)*cap (process S Y) (process H Y)-
        mixedOccupation H R S Y := by
  filter_upwards [Lp.coeFn_sub (endpoint H R S) (mixedOccupationClass H R S),
    endpoint_actual H R S,mixedOccupationClass_actual H R S] with Y ha he ho
  change reconstruction H R S Y = _ at ha
  rw [ha,Pi.sub_apply,he,ho]

def native (H R S : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  IBMJointRandomGraphIdentity.nativeOperator H N (mixedObservation R S : JointL2)

theorem native_actual (H R S : ℝ≥0) (N : ℕ) :
    native H R S N =ᵐ[gaussianProduct] fun Y =>
      mixedEnergy (H/(N+1)) (N+1) R S Y := by
  change IBMJointRandomContraction.jointOperator _ (mixedObservation R S : JointL2) =ᵐ[_] _
  rw [mixedObservation_realization,IBMJointRandomContraction.joint_realization]
  exact (IBMJointRandomContraction.source_actual _ _).trans
    (source_mixed_pairing_ae (H/(N+1)) (N+1) R S)

theorem native_identity (H R S : ℝ≥0) (N : ℕ) :
    native H R S N = endpoint H R S-mixedClass H R S N := by
  apply Lp.ext
  filter_upwards [native_actual H R S N,
    Lp.coeFn_sub (endpoint H R S) (mixedClass H R S N),
    endpoint_actual H R S,mixedClass_actual H R S N] with Y hn ha he hm
  rw [hn,ha,Pi.sub_apply,he,hm,mixedEnergy_identity]

theorem native_tendsto (H R S : ℝ≥0) (hH : 0 < H) :
    Tendsto (native H R S) atTop (𝓝 (reconstruction H R S)) := by
  have ht := (tendsto_const_nhds (x := endpoint H R S)).sub (mixedClass_tendsto H R S hH)
  exact ht.congr' (Eventually.of_forall fun N => (native_identity H R S N).symm)

theorem native_expectation (H R S : ℝ≥0) (N : ℕ) :
    L1.integralCLM (native H R S N) = nativeMixedPairing H R S N := by
  rw [native,IBMJointRandomGraphIdentity.nativeOperator,
    IBMJointRandomContraction.joint_expectation,
    nativeMixedPairing,IBMRawGridSecondChaos.native_grid_value]
  exact (IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right
    (mixedObservation R S) (jointRealization
      (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1)))).symm

theorem compatible_with_completed_test (H R S : ℝ≥0) (hH : 0 < H)
    (x : IBMJointBanachTestSpace.Tests)
    (hx : IBMJointBanachTestSpace.realize x = (mixedObservation R S : JointL2)) :
    IBMJointRandomDistribution.distribution H hH x = reconstruction H R S := by
  have ht := IBMJointRandomDistribution.native_tendsto H hH x
  have he (N : ℕ) : IBMJointRandomDistribution.nativeOperator H N x = native H R S N := by
    change IBMJointRandomGraphIdentity.nativeOperator H N (IBMJointBanachTestSpace.realize x) = _
    rw [hx]
    rfl
  exact tendsto_nhds_unique (ht.congr' (Eventually.of_forall he)) (native_tendsto H R S hH)

theorem finite_family_tendsto {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (R S : ι → ℝ≥0) (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => IBMJointRandomGraphIdentity.nativeOperator H N
      (∑ i ∈ s, a i • (mixedObservation (R i) (S i) : JointL2))) atTop
        (𝓝 (∑ i ∈ s, a i • reconstruction H (R i) (S i))) := by
  have ht := tendsto_finsetSum s (fun i _ => (native_tendsto H (R i) (S i) hH).const_smul (a i))
  simpa only [map_sum,map_smul,native] using ht

end OperatorDerivativeRewrite.Foundation.IBMActualQuadraticRandomReconstruction
