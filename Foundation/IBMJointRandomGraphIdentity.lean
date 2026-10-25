import Foundation.IBMJointRandomContraction
import Foundation.IBMJointCompletedTestGraph

/-! Full clock-L1 identities on the existing joint test graph. In particular,
annihilation of a zero joint test holds before integrating over the clock. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMJointRandomGraphIdentity
open InfiniteGaussian IBMTimeAveragedObservable IBMSpatialRandomTestBounds
open IBMJointMixedSpatialTransport IBMRawGridSecondChaos IBMJointCompletedTestGraph
open IBMSpatialCompletedTestLimit IBMSpatialMixedWickTesting IBMSpatialBoundedTestOperator

def nativeOperator (T : ℝ≥0) (N : ℕ) : JointL2 →L[ℝ] Lp ℝ 1 gaussianProduct :=
  IBMJointRandomContraction.jointOperator (sourceGrid (T/(N+1)) (N+1))

theorem generator_identity (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) (T : ℝ≥0) (N : ℕ) :
    nativeOperator T N (jointTest g h a) =
      IBMSpatialSignedRandomTests.finiteOperator T N (symbol g h a) := by
  change IBMJointRandomContraction.jointOperator _ (jointRealization (sourceTest g h a)) = _
  rw [IBMJointRandomContraction.joint_realization]
  apply Lp.ext
  filter_upwards [IBMJointRandomContraction.source_actual
    (sourceGrid (T/(N+1)) (N+1)) (sourceTest g h a),
    BochnerClosedOperator.tensor_coeFn gaussianProduct a (sceneryProbe g h),
    BochnerClosedOperator.tensor_coeFn gaussianProduct a (mixedCore g h:Completed),
    source_spatial_ae g h T N,IBMSpatialSignedRandomTests.finite_actual T N (symbol g h a)]
      with Y hv ht hu hs hf
  change sourceTest g h a Y = a Y • sceneryProbe g h at ht
  change symbol g h a Y = a Y • (mixedCore g h:Completed) at hu
  rw [hv,ht,real_inner_smul_right,hf,hu,map_smul,realize_coe]
  change a Y*inner ℝ (sourceGrid (T/(N+1)) (N+1) Y) (sceneryProbe g h) =
    IBMSpatialKernelTesting.cellPair (a Y • mixedTest g h) 0 |IBMConstructedSources.clockPath Y T|-
      finiteValue (a Y • mixedTest g h) T N Y
  rw [cellPair_smul,hs]
  have he : finiteValue (a Y • mixedTest g h) T N Y = a Y*finiteValue (mixedTest g h) T N Y := by
    unfold finiteValue
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => cellPair_smul _ _ _ _
  rw [he]
  ring

private def finiteDefect (T : ℝ≥0) (N : ℕ) :
    (JointL2 × RandomTests) →L[ℝ] Lp ℝ 1 gaussianProduct :=
  (nativeOperator T N).comp (ContinuousLinearMap.fst ℝ JointL2 RandomTests)-
    (IBMSpatialSignedRandomTests.finiteOperator T N).comp
      (ContinuousLinearMap.snd ℝ JointL2 RandomTests)

theorem finite_identity (T : ℝ≥0) (N : ℕ) (p : Graph) :
    nativeOperator T N (jointMap p) =
      IBMSpatialSignedRandomTests.finiteOperator T N (symbolMap p) := by
  have hs : Submodule.span ℝ generators ≤ (finiteDefect T N).ker := by
    apply Submodule.span_le.mpr
    rintro q ⟨g,h,a,rfl⟩
    change nativeOperator T N (jointTest g h a)-
      IBMSpatialSignedRandomTests.finiteOperator T N (symbol g h a) = 0
    rw [generator_identity,sub_self]
  have hc : testGraph ≤ (finiteDefect T N).ker :=
    (Submodule.span ℝ generators).topologicalClosure_minimal hs (finiteDefect T N).isClosed_ker
  have hp := hc p.property
  change nativeOperator T N (jointMap p)-
    IBMSpatialSignedRandomTests.finiteOperator T N (symbolMap p) = 0 at hp
  exact sub_eq_zero.mp hp

def limitOperator (T : ℝ≥0) : Graph →L[ℝ] Lp ℝ 1 gaussianProduct :=
  (IBMSpatialSignedRandomTests.limitOperator T).comp symbolMap

theorem native_tendsto (T : ℝ≥0) (hT : 0 < T) (p : Graph) :
    Tendsto (fun N => nativeOperator T N (jointMap p)) atTop (𝓝 (limitOperator T p)) :=
  (IBMSpatialSignedRandomTests.signed_random_tendsto T hT (symbolMap p)).congr'
    (Eventually.of_forall fun N => (finite_identity T N p).symm)

theorem joint_kernel_le_limit_kernel (T : ℝ≥0) (hT : 0 < T) :
    jointMap.ker ≤ (limitOperator T).ker := by
  intro p hp
  change jointMap p = 0 at hp
  change limitOperator T p = 0
  have hz : Tendsto (fun _ : ℕ => (0 : Lp ℝ 1 gaussianProduct)) atTop
      (𝓝 (limitOperator T p)) := by
    simpa only [hp,map_zero] using native_tendsto T hT p
  exact tendsto_nhds_unique hz tendsto_const_nhds

end OperatorDerivativeRewrite.Foundation.IBMJointRandomGraphIdentity
