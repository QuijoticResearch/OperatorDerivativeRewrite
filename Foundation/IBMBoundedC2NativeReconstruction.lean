import Foundation.IBMBoundedObservationSections

/-! Actual bounded C2 IBM terminal tests have source-native reconstructions
in clock L2. The coefficient is the actual scenery mean of the second jet. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMBoundedC2NativeReconstruction
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMRawStepSources
open IBMBoundedObservationSections IBMBoundedC2SecondProjection
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) {A B C : ℝ}
  (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖deriv φ x‖ ≤ B)
  (hC : ∀ x, ‖deriv (deriv φ) x‖ ≤ C)

include hφ in
theorem second_continuous : Continuous (deriv (deriv φ)) :=
  (RealSteklovApprox.deriv_contDiff_one φ hφ).continuous_deriv_one

def coefficientField (R : ℝ≥0) : GaussianL2 :=
  (1/2:ℝ) • clockMean (second_continuous hφ) hC R

theorem coefficientField_actual (R : ℝ≥0) :
    coefficientField hφ hC R =ᵐ[gaussianProduct] fun Y => coefficient φ (clockDirection R Y) := by
  filter_upwards [Lp.coeFn_smul (1/2:ℝ) (clockMean (second_continuous hφ) hC R),
    clockMean_actual (second_continuous hφ) hC R] with Y hs hm
  change coefficientField hφ hC R Y = _ at hs
  rw [hs,Pi.smul_apply,hm,smul_eq_mul]
  rfl

theorem coefficientField_bound (R : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, ‖coefficientField hφ hC R Y‖ ≤ C/2 := by
  filter_upwards [coefficientField_actual hφ hC R] with Y hY
  rw [hY]
  exact coefficient_bound hC _

private theorem weighted_memLp (R : ℝ≥0) (u : GaussianL2) :
    MemLp (fun Y => coefficientField hφ hC R Y*u Y) 2 gaussianProduct := by
  apply MemLp.of_le_mul (c := C/2) (Lp.memLp u)
    ((Lp.aestronglyMeasurable (coefficientField hφ hC R)).mul (Lp.aestronglyMeasurable u))
  filter_upwards [coefficientField_bound hφ hC R] with Y hY
  simp only [Pi.mul_apply,norm_mul]
  exact mul_le_mul_of_nonneg_right hY (norm_nonneg _)

def weighted (R : ℝ≥0) (u : GaussianL2) : GaussianL2 := (weighted_memLp hφ hC R u).toLp _

theorem weighted_actual (R : ℝ≥0) (u : GaussianL2) :
    weighted hφ hC R u =ᵐ[gaussianProduct] fun Y => coefficientField hφ hC R Y*u Y :=
  (weighted_memLp hφ hC R u).coeFn_toLp

theorem weighted_bound (R : ℝ≥0) (u : GaussianL2) :
    ‖weighted hφ hC R u‖ ≤ (C/2)*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weighted_actual hφ hC R u,coefficientField_bound hφ hC R] with Y ha hb
  rw [ha,norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

theorem weighted_sub (R : ℝ≥0) (u v : GaussianL2) :
    weighted hφ hC R (u-v) = weighted hφ hC R u-weighted hφ hC R v := by
  apply Lp.ext
  filter_upwards [weighted_actual hφ hC R (u-v),weighted_actual hφ hC R u,
    weighted_actual hφ hC R v,Lp.coeFn_sub u v,
    Lp.coeFn_sub (weighted hφ hC R u) (weighted hφ hC R v)] with Y he hu hv hi ho
  rw [he,ho,Pi.sub_apply,hu,hv,hi,Pi.sub_apply,mul_sub]

theorem weighted_tendsto (R : ℝ≥0) (u : ℕ → GaussianL2) (v : GaussianL2)
    (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun N => weighted hφ hC R (u N)) atTop (𝓝 (weighted hφ hC R v)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (tendsto_iff_norm_sub_tendsto_zero.mp hu).const_mul (C/2)
  simp only [mul_zero] at ht
  apply squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) ht
  rw [← weighted_sub]
  exact weighted_bound hφ hC R (u N-v)

def native (H R : ℝ≥0) (N : ℕ) : GaussianL2 :=
  weighted hφ hC R (IBMActualQuadraticL2Reconstruction.native H R R N)

def reconstruction (H R : ℝ≥0) : GaussianL2 :=
  weighted hφ hC R (IBMActualQuadraticL2Reconstruction.reconstruction H R R)

theorem native_actual (H R : ℝ≥0) (N : ℕ) :
    native hφ hC H R N =ᵐ[gaussianProduct] fun Y => coefficient φ (clockDirection R Y)*
      IBMRawGridMixedObservable.mixedEnergy (H/(N+1)) (N+1) R R Y := by
  filter_upwards [weighted_actual hφ hC R (IBMActualQuadraticL2Reconstruction.native H R R N),
    coefficientField_actual hφ hC R,IBMActualQuadraticL2Reconstruction.native_actual H R R N]
      with Y ha hc hn
  change native hφ hC H R N Y = _ at ha
  rw [ha,hc,hn]

theorem reconstruction_actual (H R : ℝ≥0) :
    reconstruction hφ hC H R =ᵐ[gaussianProduct] fun Y => coefficient φ (clockDirection R Y)*
      ((IBMClippedClockCrossing.cap (GaussianTimeProcess.process R Y)
        (GaussianTimeProcess.process H Y))^2-
        IBMMixedClockLimit.mixedOccupation H R R Y) := by
  filter_upwards [weighted_actual hφ hC R (IBMActualQuadraticL2Reconstruction.reconstruction H R R),
    coefficientField_actual hφ hC R,IBMActualQuadraticL2Reconstruction.reconstruction_actual H R R]
      with Y ha hc hr
  change reconstruction hφ hC H R Y = _ at ha
  rw [ha,hc,hr,pow_two]

include hA hB hC in
theorem source_native_actual (H R : ℝ≥0) (N : ℕ) :
    IBMJointRandomGraphIdentity.nativeOperator H N (jointClass hφ.continuous hA R)
      =ᵐ[gaussianProduct] fun Y => coefficient φ (clockDirection R Y)*
        IBMRawGridMixedObservable.mixedEnergy (H/(N+1)) (N+1) R R Y := by
  filter_upwards [IBMJointRandomContraction.joint_actual
      (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1)) (jointClass hφ.continuous hA R),
    source_sections hφ.continuous hA R,IBMRawGridSecondChaos.sourceGrid_ae (H/(N+1)) (N+1),
    IBMRawGridMixedObservable.mixedSource_actual R R,
    IBMRawGridMixedObservable.source_mixed_pairing_ae (H/(N+1)) (N+1) R R] with Y ha hq hs hm he
  change IBMJointRandomContraction.jointOperator
    (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1)) (jointClass hφ.continuous hA R) Y = _
  rw [ha,hq]
  have hf : IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1) Y ∈
      GaussianNumberSectors.sector 2 := by
    rw [hs]
    exact IBMRawGridSecondChaos.source_mem_sector _ _
  rw [second_pairing hφ hA hB hC _ hf]
  rw [hm] at he
  rw [he]

include hA hB in
theorem native_lower (H R : ℝ≥0) (N : ℕ) :
    IBMClippedClockStrongLimit.clockL1 (native hφ hC H R N) =
    IBMJointRandomGraphIdentity.nativeOperator H N (jointClass hφ.continuous hA R) := by
  apply Lp.ext
  exact (IBMClippedClockStrongLimit.clockL1_actual _).trans
    ((native_actual hφ hC H R N).trans (source_native_actual hφ hA hB hC H R N).symm)

theorem native_tendsto (H R : ℝ≥0) (hH : 0 < H) :
    Tendsto (native hφ hC H R) atTop (𝓝 (reconstruction hφ hC H R)) :=
  weighted_tendsto hφ hC R _ _ (IBMActualQuadraticL2Reconstruction.native_tendsto H R R hH)

include hA hB in
theorem source_native_tendsto (H R : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => IBMJointRandomGraphIdentity.nativeOperator H N
      (jointClass hφ.continuous hA R))
      atTop (𝓝 (IBMClippedClockStrongLimit.clockL1 (reconstruction hφ hC H R))) :=
  (IBMClippedClockStrongLimit.clockL1_tendsto _ _ (native_tendsto hφ hC H R hH)).congr'
    (Eventually.of_forall fun N => native_lower hφ hA hB hC H R N)

include hA in
theorem native_expectation (H R : ℝ≥0) (N : ℕ) :
    L1.integralCLM (IBMJointRandomGraphIdentity.nativeOperator H N
      (jointClass hφ.continuous hA R)) =
      inner ℝ (IBMJointIntrinsicDerivative.jointDivergence
        (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1)))
          (observation hφ.continuous hA R) := by
  change L1.integralCLM (IBMJointRandomContraction.jointOperator
    (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1)) (jointClass hφ.continuous hA R)) = _
  rw [IBMJointRandomContraction.joint_expectation,IBMRawGridSecondChaos.native_grid_value]
  exact (IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right
    (observation hφ.continuous hA R)
    (jointRealization (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1)))).symm

include hA hB in
theorem intrinsic_pairing_tendsto (H R : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N : ℕ => inner ℝ (IBMJointIntrinsicDerivative.jointDivergence
      (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))) (observation hφ.continuous hA R)) atTop
        (𝓝 (L1.integralCLM (IBMClippedClockStrongLimit.clockL1 (reconstruction hφ hC H R)))) :=
  ((L1.integralCLM (μ := gaussianProduct) (E := ℝ)).continuous.tendsto _
    |>.comp (source_native_tendsto hφ hA hB hC H R hH)).congr'
      (Eventually.of_forall fun N => native_expectation hφ hA H R N)

end OperatorDerivativeRewrite.Foundation.IBMBoundedC2NativeReconstruction
