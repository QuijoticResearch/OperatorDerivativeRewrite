import Foundation.IBMActualQuarticSourceTesting
import Foundation.IBMObservableQuartic

/-! Clock-L1 reconstruction of ORIGINAL source-native testing against an
actual intrinsic fourth-power IBM observation. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMActualQuarticRandomReconstruction
open InfiniteGaussian IBMTimeAveragedObservable GaussianTimeProcess
open IBMRawGridMixedObservable IBMClippedClockCrossing

local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

theorem fourth_observable (R : ℝ≥0) : IBMActualQuarticMoment.fourthClass R ∈ IntrinsicSpace := by
  change AEStronglyMeasurable[IBMConditionalObservable.observableSigma
    IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath]
      (IBMActualQuarticMoment.fourthClass R) IBMSourceLaws.jointMeasure
  have hm : Measurable[IBMConditionalObservable.observableSigma
      IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath]
      (fun p => (IBMConstructedSources.ibmValue R p)^4) :=
    (IBMObservableQuartic.observable_value_measurable _ _ R).pow_const 4
  exact hm.aestronglyMeasurable.congr (IBMActualQuarticMoment.fourthClass_ae R).symm

def observation (R : ℝ≥0) : IntrinsicSpace :=
  ⟨IBMActualQuarticMoment.fourthClass R,fourth_observable R⟩

def weight (R : ℝ≥0) : GaussianL2 :=
  (((process_memLp R 2 (by simp)).norm).const_mul 6).toLp _

theorem weight_actual (R : ℝ≥0) : weight R =ᵐ[gaussianProduct] fun Y => 6*|process R Y| := by
  filter_upwards [(((process_memLp R 2 (by simp)).norm).const_mul 6).coeFn_toLp] with Y hY
  change weight R Y = 6*‖process R Y‖ at hY
  simpa only [Real.norm_eq_abs] using hY

def reconstruction (H R : ℝ≥0) : Lp ℝ 1 gaussianProduct :=
  ((Lp.memLp (weight R)).integrable_mul
    (Lp.memLp (IBMActualQuadraticL2Reconstruction.reconstruction H R R))).toL1 _

theorem reconstruction_actual (H R : ℝ≥0) :
    reconstruction H R =ᵐ[gaussianProduct] fun Y => 6*|process R Y| *
      (cap (process R Y) (process H Y)*cap (process R Y) (process H Y)-
        IBMMixedClockLimit.mixedOccupation H R R Y) := by
  filter_upwards [((Lp.memLp (weight R)).integrable_mul
      (Lp.memLp (IBMActualQuadraticL2Reconstruction.reconstruction H R R))).coeFn_toL1,
    weight_actual R,IBMActualQuadraticL2Reconstruction.reconstruction_actual H R R] with Y ha hw hr
  change reconstruction H R Y = _ at ha
  rw [ha,Pi.mul_apply,hw,hr]

def native (H R : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  IBMJointRandomGraphIdentity.nativeOperator H N (observation R : JointL2)

theorem native_tendsto (H R : ℝ≥0) (hH : 0 < H) :
    Tendsto (native H R) atTop (𝓝 (reconstruction H R)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := IBMActualQuadraticL2Reconstruction.weighted_absolute_tendsto H R R hH (weight R)
  apply ht.congr'
  apply Eventually.of_forall
  intro N
  dsimp only
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [IBMActualQuarticSourceTesting.native_actual H R N,
    reconstruction_actual H R,weight_actual R,
    Lp.coeFn_sub (native H R N) (reconstruction H R)] with Y hn hr hw hs
  change native H R N Y = _ at hn
  rw [hs,Pi.sub_apply,hn,hr,hw,Real.norm_eq_abs]
  congr 1
  ring

theorem native_expectation (H R : ℝ≥0) (N : ℕ) :
    L1.integralCLM (native H R N) = inner ℝ
      (IBMJointIntrinsicDerivative.jointDivergence
        (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))) (observation R) := by
  change L1.integralCLM (IBMJointRandomContraction.jointOperator
    (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1)) (observation R : JointL2)) = _
  rw [IBMJointRandomContraction.joint_expectation,IBMRawGridSecondChaos.native_grid_value]
  exact (IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right (observation R)
    (jointRealization (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1)))).symm

theorem intrinsic_pairing_tendsto (H R : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N : ℕ => inner ℝ
      (IBMJointIntrinsicDerivative.jointDivergence
        (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))) (observation R))
      atTop (𝓝 (L1.integralCLM (reconstruction H R))) := by
  exact ((L1.integralCLM (μ := gaussianProduct) (E := ℝ)).continuous.tendsto _
    |>.comp (native_tendsto H R hH)).congr'
      (Eventually.of_forall fun N => native_expectation H R N)

end OperatorDerivativeRewrite.Foundation.IBMActualQuarticRandomReconstruction
