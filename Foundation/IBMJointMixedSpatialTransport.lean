import Foundation.IBMSpatialSignedRandomTests
import Foundation.IBMSpatialMixedWickTesting
import Foundation.BochnerClosedOperator

/-! Exact ORIGINAL joint-source pairings with arbitrary L2 clock weights
and mixed Schwartz scenery probes. Observable projection is retained unless
the test has independently established intrinsic membership. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMJointMixedSpatialTransport
open InfiniteGaussian IBMTimeAveragedObservable IBMSpatialCompletedTestLimit
open IBMSpatialMixedWickTesting IBMPhysicalWickTestDomain IBMRawGridSecondChaos
open IBMSpatialBoundedTestOperator IBMSpatialRandomTestBounds

def sceneryProbe (g h : SchwartzMap ℝ ℝ) : GaussianL2 :=
  IBMSchwartzSourceContinuity.rawProduct (testDirection g) (testDirection h)

def sourceTest (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) : ValueSpace :=
  BochnerClosedOperator.tensor gaussianProduct a (sceneryProbe g h)

def jointTest (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) : JointL2 :=
  jointRealization (sourceTest g h a)

def symbol (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) : RandomTests :=
  BochnerClosedOperator.tensor gaussianProduct a (mixedCore g h:Completed)

theorem jointTest_actual (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) :
    jointTest g h a =ᵐ[IBMSourceLaws.jointMeasure] fun p => a p.2*
      firstChaosEmbedding (testDirection g) p.1*firstChaosEmbedding (testDirection h) p.1 := by
  apply jointRealization_ae_of_sections
  · exact (((Lp.stronglyMeasurable a).measurable.comp measurable_snd).mul
      ((Lp.stronglyMeasurable (firstChaosEmbedding (testDirection g))).measurable.comp measurable_fst)).mul
        ((Lp.stronglyMeasurable (firstChaosEmbedding (testDirection h))).measurable.comp measurable_fst)
  · filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct a (sceneryProbe g h)] with Y hY
    change sourceTest g h a Y = a Y • sceneryProbe g h at hY
    rw [hY]
    filter_upwards [Lp.coeFn_smul (a Y) (sceneryProbe g h),
      IBMSchwartzSourceContinuity.rawProduct_coeFn (testDirection g) (testDirection h)] with X hs hp
    rw [hs,Pi.smul_apply,smul_eq_mul]
    change a Y*IBMSchwartzSourceContinuity.rawProduct (testDirection g) (testDirection h) X = _
    rw [hp]
    ring

theorem source_spatial_ae (g h : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) :
    (fun Y => inner ℝ (sourceGrid (T/(N+1)) (N+1) Y) (sceneryProbe g h)) =ᵐ[gaussianProduct]
      fun Y => IBMSpatialKernelTesting.cellPair (mixedTest g h) 0 |IBMConstructedSources.clockPath Y T|-
        finiteValue (mixedTest g h) T N Y := by
  have he := source_signed_identity g h T N
  filter_upwards [IBMClippedClockStrongLimit.clockL1_actual (sourceAction g h T N),
    IBMSpatialSignedReconstruction.finite_actual T N (mixedCore g h:Completed),
    (innerSL ℝ (sceneryProbe g h)).coeFn_compLpL (sourceGrid (T/(N+1)) (N+1)),
    IBMConstructedSources.clockPath_coordinate_ae T] with Y hl hf ha hc
  have hp := congrArg (fun v : Lp ℝ 1 gaussianProduct => v Y) he
  rw [hl,hf,realize_coe] at hp
  change sourceAction g h T N Y = _ at ha
  rw [ha] at hp
  change inner ℝ (sceneryProbe g h) (sourceGrid (T/(N+1)) (N+1) Y) =
    IBMSpatialKernelTesting.cellPair (mixedTest g h) 0 |GaussianTimeProcess.process T Y|-
      finiteValue (mixedTest g h) T N Y at hp
  rw [real_inner_comm,hc]
  exact hp

theorem original_source_pairing (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) (T : ℝ≥0) (N : ℕ) :
    inner ℝ (sourceGrid (T/(N+1)) (N+1)) (sourceTest g h a) =
      ∫ Y, IBMSpatialSignedRandomTests.finiteOperator T N (symbol g h a) Y ∂gaussianProduct := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct a (sceneryProbe g h),
    BochnerClosedOperator.tensor_coeFn gaussianProduct a (mixedCore g h:Completed),
    source_spatial_ae g h T N,IBMSpatialSignedRandomTests.finite_actual T N (symbol g h a)] with Y ht hu hs hf
  change sourceTest g h a Y = a Y • sceneryProbe g h at ht
  change symbol g h a Y = a Y • (mixedCore g h:Completed) at hu
  rw [ht,real_inner_smul_right,hf,hu,map_smul,realize_coe]
  change a Y*inner ℝ (sourceGrid (T/(N+1)) (N+1) Y) (sceneryProbe g h) =
    IBMSpatialKernelTesting.cellPair (a Y • mixedTest g h) 0 |IBMConstructedSources.clockPath Y T|-
      finiteValue (a Y • mixedTest g h) T N Y
  rw [IBMSpatialBoundedTestOperator.cellPair_smul,hs]
  have he : finiteValue (a Y • mixedTest g h) T N Y = a Y*finiteValue (mixedTest g h) T N Y := by
    unfold finiteValue
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => IBMSpatialBoundedTestOperator.cellPair_smul _ _ _ _
  rw [he]
  ring

theorem original_joint_pairing (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) (T : ℝ≥0) (N : ℕ) :
    inner ℝ (jointRealization (sourceGrid (T/(N+1)) (N+1))) (jointTest g h a) =
      ∫ Y, IBMSpatialSignedRandomTests.finiteOperator T N (symbol g h a) Y ∂gaussianProduct := by
  rw [jointTest,jointRealization.inner_map_map]
  exact original_source_pairing g h a T N

def limitingPairing (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) (T : ℝ≥0) : ℝ :=
  ∫ Y, IBMSpatialSignedRandomTests.limitOperator T (symbol g h a) Y ∂gaussianProduct

theorem original_joint_pairing_tendsto (g h : SchwartzMap ℝ ℝ) (a : GaussianL2)
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun N : ℕ => inner ℝ (jointRealization (sourceGrid (T/(N+1)) (N+1))) (jointTest g h a))
      atTop (𝓝 (limitingPairing g h a T)) := by
  have ht := (L1.integralCLM (μ := gaussianProduct) (E := ℝ)).continuous.tendsto
    (IBMSpatialSignedRandomTests.limitOperator T (symbol g h a))
  have hh := ht.comp (IBMSpatialSignedRandomTests.signed_random_tendsto T hT (symbol g h a))
  have hi : Tendsto (fun N => ∫ Y, IBMSpatialSignedRandomTests.finiteOperator T N (symbol g h a) Y ∂gaussianProduct)
      atTop (𝓝 (limitingPairing g h a T)) := by
    simpa only [Function.comp_def,← L1.integral_eq,L1.integral_eq_integral,limitingPairing] using hh
  exact hi.congr' (Eventually.of_forall fun N => (original_joint_pairing g h a T N).symm)

local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _ IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

theorem intrinsic_pairing_tendsto (g h : SchwartzMap ℝ ℝ) (a : GaussianL2)
    (T : ℝ≥0) (hT : 0 < T) (v : IntrinsicSpace) (hv : (v:JointL2) = jointTest g h a) :
    Tendsto (fun N : ℕ => inner ℝ
      (IBMJointIntrinsicDerivative.jointDivergence (IBMRawGridCompensation.gridInput (T/(N+1)) (N+1))) v)
      atTop (𝓝 (limitingPairing g h a T)) := by
  have he (N : ℕ) : inner ℝ
      (IBMJointIntrinsicDerivative.jointDivergence (IBMRawGridCompensation.gridInput (T/(N+1)) (N+1))) v =
        inner ℝ (jointRealization (sourceGrid (T/(N+1)) (N+1))) (jointTest g h a) := by
    rw [native_grid_value]
    have hp := IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right v
      (jointRealization (sourceGrid (T/(N+1)) (N+1)))
    rw [hp,hv]
  exact (original_joint_pairing_tendsto g h a T hT).congr' (Eventually.of_forall fun N => (he N).symm)

theorem finite_family_pairing_tendsto {ι : Type*} (s : Finset ι)
    (g h : ι → SchwartzMap ℝ ℝ) (a : ι → GaussianL2) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun N : ℕ => inner ℝ (jointRealization (sourceGrid (T/(N+1)) (N+1)))
      (∑ i ∈ s, jointTest (g i) (h i) (a i))) atTop
        (𝓝 (∑ i ∈ s, limitingPairing (g i) (h i) (a i) T)) := by
  have ht := tendsto_finsetSum s (fun i _ => original_joint_pairing_tendsto (g i) (h i) (a i) T hT)
  simpa only [inner_sum] using ht

end OperatorDerivativeRewrite.Foundation.IBMJointMixedSpatialTransport
