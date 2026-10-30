import Foundation.CubeBoundaryChartInverse

/-! Literal kernel of the actual compressed Wilson transfer on its entire Euclidean L2 domain. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.CubeChartCompressedKernel
open CubeTemporalSlab CubeWilsonSlab CubeSlabGround CubeAxialSlice CubeHaarSplit CubeChartAction
open CubeChordOperator CubeBoundaryChartMeasure CubeBoundaryChartL2 CubeBoundaryChartInverse
attribute [local irreducible] CubeWilsonSlab.kernel

def scaledIntegrand (t : ℝ) (F : EuclideanL2) (q : Chords) (Y : Boundary) : ℝ :=
  CubeBoundaryHaarL2.density (t • Y)*(CubeBoundaryKernelL2.cutoff t).indicator
    (fun Y => kernel (1/t^2) (axialState q) (boundaryRay Y t)*inverseFunction t F (chords Y t)) Y

private theorem integrand_measurable (t : ℝ) (F : EuclideanL2) (q : Chords) :
    Measurable (fun r : Chords => kernel (1/t^2) (axialState q) (axialState r)*inverseFunction t F r) :=
  (((kernel_joint_measurable (1/t^2)).comp (measurable_const.prodMk CubeChordTransfer.axial_measurable)).mul
    (inverseFunction_measurable t F (Lp.stronglyMeasurable F).measurable))

theorem scaledIntegrand_integrable (t : ℝ) (ht : 0 < t) (F : EuclideanL2) (q : Chords) :
    Integrable (scaledIntegrand t F q) := by
  have hi : Integrable (fun r : Chords =>
      kernel (1/t^2) (axialState q) (axialState r)*inverseFunction t F r) chordHaar := by
    apply (rawChord_integrable (beta := 1/t^2) (backward t ht F) q).congr
    filter_upwards [backward_coe t ht F] with r hr
    rw [hr]
  exact (scaled_local_integrable_iff _ (integrand_measurable t F q) t ht.ne').mp hi.integrableOn

theorem rawChord_inverse_scaled (t : ℝ) (ht : 0 < t) (F : EuclideanL2) (q : Chords) :
    rawChord (beta := 1/t^2) (backward t ht F) q=t^15*(∫ Y : Boundary,scaledIntegrand t F q Y) := by
  unfold rawChord
  calc
    _ = ∫ r,kernel (1/t^2) (axialState q) (axialState r)*inverseFunction t F r ∂chordHaar := by
      apply integral_congr_ae
      filter_upwards [backward_coe t ht F] with r hr
      rw [hr]
    _ = ∫ r in CubeBoundaryExterior.chordRegion,
        kernel (1/t^2) (axialState q) (axialState r)*inverseFunction t F r ∂chordHaar := by
      rw [← integral_indicator CubeBoundaryExterior.chordRegion_measurable]
      apply integral_congr_ae
      filter_upwards with r
      classical
      by_cases hr : r ∈ CubeBoundaryExterior.chordRegion
      · rw [Set.indicator_of_mem hr]
      · simp only [Set.indicator_of_notMem hr,inverseFunction,mul_zero]
    _ = _ := integral_local_scaled _ (integrand_measurable t F q) t ht

private theorem sqrt_product (t : ℝ) (ht : 0 < t) (X Y : Boundary) :
    Real.sqrt (CubeBoundaryChartInverse.weight t X)*Real.sqrt (CubeBoundaryChartInverse.weight t Y)=t^15*CubeBoundaryHaarL2.halfDensity t (X,Y) := by
  rw [← Real.sqrt_mul (weight_positive t ht X).le]
  have he : CubeBoundaryChartInverse.weight t X*CubeBoundaryChartInverse.weight t Y=(t^15)^2*
      (CubeBoundaryHaarL2.density (t • X)*CubeBoundaryHaarL2.density (t • Y)) := by unfold CubeBoundaryChartInverse.weight; ring
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (pow_pos ht 15).le]
  rfl

private theorem weight_ratio (t : ℝ) (ht : 0 < t) (X Y : Boundary) :
    Real.sqrt (CubeBoundaryChartInverse.weight t X)*CubeBoundaryHaarL2.density (t • Y)/Real.sqrt (CubeBoundaryChartInverse.weight t Y)=
      CubeBoundaryHaarL2.halfDensity t (X,Y) := by
  apply (div_eq_iff (Real.sqrt_pos.mpr (weight_positive t ht Y)).ne').mpr
  apply (mul_left_cancel₀ (pow_pos ht 15).ne')
  calc
    _ = Real.sqrt (CubeBoundaryChartInverse.weight t X)*CubeBoundaryChartInverse.weight t Y := by unfold CubeBoundaryChartInverse.weight; ring
    _ = Real.sqrt (CubeBoundaryChartInverse.weight t X)*(Real.sqrt (CubeBoundaryChartInverse.weight t Y))^2 := by
      rw [Real.sq_sqrt (weight_positive t ht Y).le]
    _ = (Real.sqrt (CubeBoundaryChartInverse.weight t X)*Real.sqrt (CubeBoundaryChartInverse.weight t Y))*Real.sqrt (CubeBoundaryChartInverse.weight t Y) := by ring
    _ = _ := by rw [sqrt_product t ht]; ring

private theorem row_identity (t : ℝ) (ht : 0 < t) (F : EuclideanL2) (X Y : Boundary)
    (hX : X ∈ CubeBoundaryKernelL2.cutoff t) :
    (Real.sqrt (CubeBoundaryChartInverse.weight t X)*t^15/t^36)*scaledIntegrand t F (chords X t) Y=
      CubeBoundaryHaarL2.kernel t (X,Y)*F Y := by
  classical
  by_cases hY : Y ∈ CubeBoundaryKernelL2.cutoff t
  · unfold scaledIntegrand
    rw [Set.indicator_of_mem hY,inverse_on_chart t ht F Y hY]
    have hp : (X,Y) ∈ CubeBoundaryKernelL2.cutoff t ×ˢ CubeBoundaryKernelL2.cutoff t := ⟨hX,hY⟩
    unfold CubeBoundaryHaarL2.kernel CubeBoundaryKernelL2.localKernel
    rw [Set.indicator_of_mem hp]
    have htR : t^15/t^36=1/t^21 := by field_simp [ht.ne'] <;> ring
    calc
      _ = (t^15/t^36)*(Real.sqrt (CubeBoundaryChartInverse.weight t X)*CubeBoundaryHaarL2.density (t • Y)/
          Real.sqrt (CubeBoundaryChartInverse.weight t Y))*(kernel (1/t^2) (axialState (chords X t)) (boundaryRay Y t)*F Y) := by ring
      _ = _ := by
        rw [weight_ratio t ht,htR]
        unfold boundaryRay
        ring
  · have hp : (X,Y) ∉ CubeBoundaryKernelL2.cutoff t ×ˢ CubeBoundaryKernelL2.cutoff t :=
      fun h => hY h.2
    simp only [scaledIntegrand,Set.indicator_of_notMem hY,mul_zero,
      CubeBoundaryHaarL2.kernel,CubeBoundaryKernelL2.localKernel,Set.indicator_of_notMem hp,zero_mul]

private theorem outside_row (t : ℝ) (X Y : Boundary) (hX : X ∉ CubeBoundaryKernelL2.cutoff t) :
    CubeBoundaryHaarL2.kernel t (X,Y)=0 := by
  have hp : (X,Y) ∉ CubeBoundaryKernelL2.cutoff t ×ˢ CubeBoundaryKernelL2.cutoff t := fun h => hX h.1
  simp only [CubeBoundaryHaarL2.kernel,CubeBoundaryKernelL2.localKernel,Set.indicator_of_notMem hp,mul_zero]

theorem kernel_row_integrable (t : ℝ) (ht : 0 < t) (F : EuclideanL2) (X : Boundary) :
    Integrable (fun Y : Boundary => CubeBoundaryHaarL2.kernel t (X,Y)*F Y) := by
  classical
  by_cases hX : X ∈ CubeBoundaryKernelL2.cutoff t
  · convert (scaledIntegrand_integrable t ht F (chords X t)).const_mul
      (Real.sqrt (CubeBoundaryChartInverse.weight t X)*t^15/t^36) using 1
    funext Y
    exact (row_identity t ht F X Y hX).symm
  · have he : (fun Y : Boundary => CubeBoundaryHaarL2.kernel t (X,Y)*F Y)=0 := by
      funext Y
      simp only [outside_row t X Y hX,zero_mul,Pi.zero_apply]
    rw [he]
    exact integrable_zero _ _ _

def raw (t : ℝ) (F : EuclideanL2) (X : Boundary) : ℝ :=
  ∫ Y : Boundary,CubeBoundaryHaarL2.kernel t (X,Y)*F Y

def compressed (t : ℝ) (ht : 0 < t) (d : GroundData (1/t^2)) : EuclideanL2 →L[ℝ] EuclideanL2 :=
  (d.value/t^36) • ((forward t ht).comp ((chordOperator d).comp (backward t ht)))

/-- The ACTUAL compressed bare transfer, with all density/Jacobian factors, on all L2 inputs. -/
theorem compressed_coe (t : ℝ) (ht : 0 < t) (d : GroundData (1/t^2)) (F : EuclideanL2) :
    compressed t ht d F =ᵐ[volume] raw t F := by
  change (d.value/t^36) • forward t ht (chordOperator d (backward t ht F)) =ᵐ[volume] raw t F
  filter_upwards [Lp.coeFn_smul (d.value/t^36) (forward t ht (chordOperator d (backward t ht F))),
    forward_coe t ht (chordOperator d (backward t ht F)),
    scaled_ae_comp (chordOperator_coe d (backward t ht F)) t ht.ne'] with X hS hV hB
  rw [hS]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hV]
  classical
  by_cases hX : X ∈ CubeBoundaryKernelL2.cutoff t
  · simp only [pullback,Set.indicator_of_mem hX]
    change chordOperator d (backward t ht F) (chords X t)=
      rawChord (beta := 1/t^2) (backward t ht F) (chords X t)/d.value at hB
    rw [hB,rawChord_inverse_scaled t ht F (chords X t)]
    calc
      _ = (Real.sqrt (CubeBoundaryChartInverse.weight t X)*t^15/t^36)*(∫ Y : Boundary,scaledIntegrand t F (chords X t) Y) := by
        unfold CubeBoundaryChartInverse.weight
        field_simp [d.value_pos.ne']
        <;> ring
      _ = _ := by
        rw [raw,← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with Y
        exact row_identity t ht F X Y hX
  · simp only [pullback,Set.indicator_of_notMem hX,mul_zero]
    unfold raw
    simp only [outside_row t X _ hX,zero_mul,integral_zero]

theorem raw_memLp (t : ℝ) (ht : 0 < t) (d : GroundData (1/t^2)) (F : EuclideanL2) :
    MemLp (raw t F) 2 volume :=
  (memLp_congr_ae (compressed_coe t ht d F)).mp (Lp.memLp (compressed t ht d F))

theorem pairing_integrable (t : ℝ) (ht : 0 < t) (d : GroundData (1/t^2)) (F G : EuclideanL2) :
    Integrable (fun X : Boundary => G X*raw t F X) :=
  (Lp.memLp G).integrable_mul (raw_memLp t ht d F)

theorem compressed_kernel_pairing (t : ℝ) (ht : 0 < t) (d : GroundData (1/t^2)) (F G : EuclideanL2) :
    inner ℝ (compressed t ht d F) G=
      ∫ X : Boundary,G X*(∫ Y : Boundary,CubeBoundaryHaarL2.kernel t (X,Y)*F Y) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [compressed_coe t ht d F] with X hX
  rw [hX,Real.inner_apply]
  unfold raw
  ring

theorem compressed_ground_independent (t : ℝ) (ht : 0 < t) (d e : GroundData (1/t^2)) :
    compressed t ht d=compressed t ht e := by
  apply ContinuousLinearMap.ext
  intro F
  apply Lp.ext
  exact (compressed_coe t ht d F).trans (compressed_coe t ht e F).symm

theorem compressed_selfadjoint (t : ℝ) (ht : 0 < t) (d : GroundData (1/t^2)) :
    (compressed t ht d).adjoint=compressed t ht d := by
  simp [compressed,backward,ContinuousLinearMap.adjoint_comp,
    chordOperator_selfadjoint,ContinuousLinearMap.comp_assoc]

end OperatorDerivativeRewrite.Foundation.CubeChartCompressedKernel
