import Foundation.CubeGaussianRootGround

/-! An actual nonzero L2 Gaussian eigenvector of the root-averaged limiting operator. -/
noncomputable section
open MeasureTheory
open scoped Quaternion Matrix Matrix.Norms.Operator ENNReal
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianGroundEigenvector
open CubeGaussianModes CubeGaussianChannelGround CubeGaussianRootGround CubeChartAction
open CubeGaussianCoordinateMeasure CubeGaussianKernelChannels CubeCompressedNormLimit
open CubeBoundaryChartL2 SU2GaussianConeCoordinates SU2HemisphereJets

theorem analysis_continuous : Continuous analysis := by
  apply continuous_pi
  intro i
  unfold analysis
  apply continuous_finset_sum
  intro j _
  exact (continuous_const : Continuous (fun _ : Boundary => inverseBasis i j)).smul
    (continuous_apply j : Continuous (fun X : Boundary => X j))

def coordinateEquiv : Boundary ≃ᵐ Boundary where
  toEquiv := ⟨synthesis,analysis,analysis_synthesis,synthesis_analysis⟩
  measurable_toFun := synthesis_continuous.measurable
  measurable_invFun := analysis_continuous.measurable

/-- The explicit measurable inverse permits the change of variables for arbitrary functions. -/
theorem coordinate_integral (f : Boundary → ℝ) :
    (∫ X,f X)=64*(∫ x,f (synthesis x)) := by
  have h := coordinateEquiv.measurableEmbedding.integral_map (μ := (volume : Measure Boundary)) f
  change (∫ X,f X ∂Measure.map synthesis volume)=(∫ x,f (synthesis x)) at h
  rw [synthesis_map,integral_smul_measure] at h
  norm_num at h
  linarith

theorem gaussianState_memLp : MemLp gaussianState 2 (volume : Measure Boundary) := by
  apply (memLp_two_iff_integrable_sq gaussianState_continuous.measurable.aestronglyMeasurable).mpr
  have hi := Integrable.fintype_prod (fun i : Fin 5 =>
    gaussian_integrable (2*width i) (mul_pos (by norm_num) (width_positive i)))
  rw [← volume_pi] at hi
  convert hi using 1
  funext x
  unfold gaussianState
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [pow_two,← Real.exp_add]
  congr 1
  ring

def actualState (X : Boundary) : ℝ := gaussianState (analysis X)

theorem actualState_continuous : Continuous actualState :=
  gaussianState_continuous.comp analysis_continuous

theorem actualState_memLp : MemLp actualState 2 (volume : Measure Boundary) := by
  apply (memLp_two_iff_integrable_sq actualState_continuous.measurable.aestronglyMeasurable).mpr
  apply (synthesis_integrable_iff (fun X => actualState X^2)
    (actualState_continuous.pow 2).measurable).mp
  simpa only [actualState,analysis_synthesis] using gaussianState_memLp.integrable_sq

def stateClass : EuclideanL2 := actualState_memLp.toLp actualState

theorem stateClass_coe : stateClass =ᵐ[volume] actualState := MemLp.coeFn_toLp _

theorem stateClass_nonzero : stateClass ≠ 0 := by
  intro he
  have hz : (stateClass : Boundary → ℝ)=ᵐ[volume] (fun _ => 0) := by
    rw [he]
    exact Lp.coeFn_zero ℝ 2 volume
  have hp : ∀ᵐ X ∂(volume : Measure Boundary),0 < stateClass X := by
    filter_upwards [stateClass_coe] with X hX
    rw [hX]
    exact gaussianState_positive (analysis X)
  obtain ⟨X,hX,hP⟩ := (hz.and hp).exists
  change stateClass X=0 at hX
  linarith

def eigenvalue : ℝ := 64*constant*stateMass

theorem constant_positive : 0 < constant := by
  unfold constant SU2GaussianConeCoordinates.chartDensity
  have h := CubeSchurIntegral.temporalConstant_positive
  have hr := chartRate_positive (0 : Triple)
  positivity

theorem eigenvalue_positive : 0 < eigenvalue :=
  mul_pos (mul_pos (by norm_num) constant_positive) stateMass_positive

theorem actual_row_ground (X : Boundary) :
    (∫ Y : Boundary,CubeBoundaryHaarL2.limit (X,Y)*actualState Y)=eigenvalue*actualState X := by
  rw [coordinate_integral]
  have he (y : Boundary) : CubeBoundaryHaarL2.limit (X,synthesis y)*actualState (synthesis y)=
      constant*averaged (analysis X) y := by
    rw [actual_kernel_channels]
    simp only [actualState,analysis_synthesis,averaged]
    ring
  simp_rw [he]
  rw [integral_const_mul,averaged_ground_integral]
  unfold eigenvalue actualState
  ring

theorem actual_row_ground_integrable (X : Boundary) :
    Integrable (fun Y : Boundary => CubeBoundaryHaarL2.limit (X,Y)*actualState Y) := by
  by_contra hn
  have h := actual_row_ground X
  rw [integral_undef hn] at h
  have hp := mul_pos eigenvalue_positive (gaussianState_positive (analysis X))
  change 0=eigenvalue*gaussianState (analysis X) at h
  linarith

theorem actual_operator_eigenvector :
    actualLimitOperator stateClass=eigenvalue • stateClass := by
  apply ext_inner_right ℝ
  intro G
  rw [actualLimitOperator_integral_pairing,real_inner_smul_left,L2.inner_def,
    ← integral_const_mul]
  have hrow (X : Boundary) :
      (∫ Y : Boundary,CubeBoundaryHaarL2.limit (X,Y)*stateClass Y)=eigenvalue*actualState X := by
    rw [← actual_row_ground X]
    apply integral_congr_ae
    filter_upwards [stateClass_coe] with Y hY
    rw [hY]
  simp_rw [hrow]
  apply integral_congr_ae
  filter_upwards [stateClass_coe] with X hX
  rw [hX,Real.inner_apply]
  ring

theorem eigenvalue_le_norm : eigenvalue ≤ ‖actualLimitOperator‖ := by
  have h := actualLimitOperator.le_opNorm stateClass
  rw [actual_operator_eigenvector,norm_smul,Real.norm_eq_abs,
    abs_of_pos eigenvalue_positive] at h
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr stateClass_nonzero)).mp h

theorem normalized_operator_eigenvector :
    CubeGroundNormLimit.normalizedLimitOperator stateClass=
      (eigenvalue/‖actualLimitOperator‖) • stateClass := by
  simp only [CubeGroundNormLimit.normalizedLimitOperator,smul_apply,
    actual_operator_eigenvector,smul_smul]
  congr 1
  ring

theorem normalized_eigenvalue_bounds :
    0 < eigenvalue/‖actualLimitOperator‖ ∧ eigenvalue/‖actualLimitOperator‖ ≤ 1 := by
  constructor
  · exact div_pos eigenvalue_positive CubeGroundNormLimit.limit_norm_positive
  · exact (div_le_one₀ CubeGroundNormLimit.limit_norm_positive).mpr eigenvalue_le_norm

end OperatorDerivativeRewrite.Foundation.CubeGaussianGroundEigenvector
