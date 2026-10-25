import Foundation.IBMFiniteRidgeQuadraticTesting
import Mathlib.MeasureTheory.Function.Holder

/-! Nonlinear ACTUAL finite-ridge IBM testing, with all mixed-time kernels.
Bounded curvature coefficients act through Mathlib's Holder multiplication. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFiniteRidgeNativeReconstruction
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMFiniteRidgeObservation
open IBMBoundedC2SecondProjection
variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (r : ι → ℝ≥0)
variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) {A B C : ℝ}
  (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖deriv φ x‖ ≤ B)
  (hC : ∀ x, ‖deriv (deriv φ) x‖ ≤ C)
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

def coefficientField : GaussianL2 :=
  (1/2:ℝ) • clockMean a r (IBMBoundedC2NativeReconstruction.second_continuous hφ) hC

theorem coefficientField_actual : coefficientField a r hφ hC =ᵐ[gaussianProduct]
    fun Y => coefficient φ (direction a r Y) := by
  filter_upwards [Lp.coeFn_smul (1/2:ℝ)
      (clockMean a r (IBMBoundedC2NativeReconstruction.second_continuous hφ) hC),
    clockMean_actual a r (IBMBoundedC2NativeReconstruction.second_continuous hφ) hC] with Y hs hm
  change coefficientField a r hφ hC Y = _ at hs
  rw [hs,Pi.smul_apply,hm,smul_eq_mul]
  rfl

theorem coefficientField_bound : ∀ᵐ Y ∂gaussianProduct, ‖coefficientField a r hφ hC Y‖ ≤ C/2 := by
  filter_upwards [coefficientField_actual a r hφ hC] with Y hY
  rw [hY]
  exact coefficient_bound hC _

def coefficientInfinity : Lp ℝ ∞ gaussianProduct :=
  (MemLp.of_bound (Lp.aestronglyMeasurable (coefficientField a r hφ hC)) (C/2)
    (coefficientField_bound a r hφ hC)).toLp _

theorem coefficientInfinity_actual : coefficientInfinity a r hφ hC =ᵐ[gaussianProduct]
    fun Y => coefficient φ (direction a r Y) :=
  (MemLp.coeFn_toLp _).trans (coefficientField_actual a r hφ hC)

def multiplier : GaussianL2 →L[ℝ] GaussianL2 :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL gaussianProduct ∞ 2 2 (coefficientInfinity a r hφ hC)

theorem multiplier_actual (u : GaussianL2) : multiplier a r hφ hC u =ᵐ[gaussianProduct]
    fun Y => coefficient φ (direction a r Y)*u Y := by
  have ha := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2)
    (coefficientInfinity a r hφ hC) u
  filter_upwards [ha,coefficientInfinity_actual a r hφ hC] with Y ha hc
  change multiplier a r hφ hC u Y = _ at ha
  rw [ha,hc]
  rfl

def native (H : ℝ≥0) (N : ℕ) : GaussianL2 :=
  multiplier a r hφ hC (IBMFiniteRidgeQuadraticTesting.native a r H N)

def reconstruction (H : ℝ≥0) : GaussianL2 :=
  multiplier a r hφ hC (IBMFiniteRidgeQuadraticTesting.reconstruction a r H)

theorem reconstruction_actual (H : ℝ≥0) : reconstruction a r hφ hC H =ᵐ[gaussianProduct]
    fun Y => coefficient φ (direction a r Y)*IBMFiniteRidgeQuadraticTesting.limitValue a r H Y := by
  filter_upwards [multiplier_actual a r hφ hC (IBMFiniteRidgeQuadraticTesting.reconstruction a r H),
    IBMFiniteRidgeQuadraticTesting.reconstruction_actual a r H] with Y ha hr
  change reconstruction a r hφ hC H Y = _ at ha
  rw [ha,hr]

theorem native_actual (H : ℝ≥0) (N : ℕ) : native a r hφ hC H N =ᵐ[gaussianProduct]
    fun Y => coefficient φ (direction a r Y)*IBMFiniteRidgeQuadraticTesting.native a r H N Y :=
  multiplier_actual a r hφ hC _

include hA hB hC in
theorem source_native_actual (H : ℝ≥0) (N : ℕ) :
    IBMJointRandomGraphIdentity.nativeOperator H N (jointClass a r hφ.continuous hA)
      =ᵐ[gaussianProduct] fun Y => coefficient φ (direction a r Y)*
        IBMFiniteRidgeQuadraticTesting.native a r H N Y := by
  filter_upwards [IBMJointRandomContraction.joint_actual
      (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1)) (jointClass a r hφ.continuous hA),
    source_sections a r hφ.continuous hA,IBMRawGridSecondChaos.sourceGrid_ae (H/(N+1)) (N+1),
    IBMFiniteRidgeQuadraticTesting.source_pairing_actual a r H N] with Y ha hq hs he
  change IBMJointRandomContraction.jointOperator
    (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1)) (jointClass a r hφ.continuous hA) Y = _
  rw [ha,hq]
  have hf : IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1) Y ∈
      GaussianNumberSectors.sector 2 := by
    rw [hs]
    exact IBMRawGridSecondChaos.source_mem_sector _ _
  rw [second_pairing hφ hA hB hC _ hf,he]

include hA hB in
theorem native_lower (H : ℝ≥0) (N : ℕ) :
    IBMClippedClockStrongLimit.clockL1 (native a r hφ hC H N) =
      IBMJointRandomGraphIdentity.nativeOperator H N (jointClass a r hφ.continuous hA) := by
  apply Lp.ext
  exact (IBMClippedClockStrongLimit.clockL1_actual _).trans
    ((native_actual a r hφ hC H N).trans (source_native_actual a r hφ hA hB hC H N).symm)

theorem native_tendsto (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (native a r hφ hC H) atTop (𝓝 (reconstruction a r hφ hC H)) :=
  (multiplier a r hφ hC).continuous.tendsto _ |>.comp
    (IBMFiniteRidgeQuadraticTesting.native_tendsto a r H hH)

include hA hB in
theorem source_native_tendsto (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => IBMJointRandomGraphIdentity.nativeOperator H N
      (jointClass a r hφ.continuous hA))
      atTop (𝓝 (IBMClippedClockStrongLimit.clockL1 (reconstruction a r hφ hC H))) :=
  (IBMClippedClockStrongLimit.clockL1_tendsto _ _ (native_tendsto a r hφ hC H hH)).congr'
    (Eventually.of_forall fun N => native_lower a r hφ hA hB hC H N)

include hA in
theorem native_expectation (H : ℝ≥0) (N : ℕ) :
    L1.integralCLM (IBMJointRandomGraphIdentity.nativeOperator H N
      (jointClass a r hφ.continuous hA)) =
      inner ℝ (IBMJointIntrinsicDerivative.jointDivergence
        (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))) (observation a r hφ.continuous hA) := by
  change L1.integralCLM (IBMJointRandomContraction.jointOperator
    (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1)) (jointClass a r hφ.continuous hA)) = _
  rw [IBMJointRandomContraction.joint_expectation,IBMRawGridSecondChaos.native_grid_value]
  exact (IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right
    (observation a r hφ.continuous hA)
    (jointRealization (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1)))).symm

include hA hB in
theorem intrinsic_pairing_tendsto (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N : ℕ => inner ℝ (IBMJointIntrinsicDerivative.jointDivergence
      (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))) (observation a r hφ.continuous hA)) atTop
        (𝓝 (L1.integralCLM (IBMClippedClockStrongLimit.clockL1 (reconstruction a r hφ hC H)))) :=
  ((L1.integralCLM (μ := gaussianProduct) (E := ℝ)).continuous.tendsto _
    |>.comp (source_native_tendsto a r hφ hA hB hC H hH)).congr'
      (Eventually.of_forall fun N => native_expectation a r hφ hA H N)

end OperatorDerivativeRewrite.Foundation.IBMFiniteRidgeNativeReconstruction
