import Foundation.CubeBoundaryChartL2

/-! Explicit adjoint of the genuine boundary half-density map on all Euclidean L2 inputs. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.CubeBoundaryChartInverse
open SU2GaussianConeCoordinates SU2HemisphereChart CubeAxialSlice CubeHaarSplit
open CubeChartAction CubeChordOperator CubeBoundaryExterior CubeBoundaryChartMeasure CubeBoundaryChartL2

def coords (q : Chords) : Boundary := fun i => coordinates (q i)
def weight (t : ℝ) (X : Boundary) : ℝ := t^15*CubeBoundaryHaarL2.density (t • X)
def inverseFunction (t : ℝ) (F : Boundary → ℝ) (q : Chords) : ℝ :=
  chordRegion.indicator (fun q => F (t⁻¹ • coords q)/
    Real.sqrt (t^15*CubeBoundaryHaarL2.density (coords q))) q

theorem coords_measurable : Measurable coords :=
  measurable_pi_iff.mpr (fun i => coordinates_measurable.comp (measurable_pi_apply i))

theorem coords_chords (X : Boundary) (t : ℝ) : coords (chords X t)=t • X := by
  funext i
  exact coordinates_chart (t • X i)

theorem weight_positive (t : ℝ) (ht : 0 < t) (X : Boundary) : 0 < weight t X :=
  mul_pos (pow_pos ht 15) (CubeBoundaryHaarL2.density_positive _)

theorem inverseFunction_measurable (t : ℝ) (F : Boundary → ℝ) (hF : Measurable F) :
    Measurable (inverseFunction t F) := by
  have hn := hF.comp (coords_measurable.const_smul t⁻¹)
  have hd := ((measurable_const : Measurable (fun _ : Chords => t^15)).mul
    (CubeBoundaryHaarL2.density_continuous.measurable.comp coords_measurable)).sqrt
  exact (hn.div hd).indicator chordRegion_measurable

theorem inverse_on_chart (t : ℝ) (ht : 0 < t) (F : Boundary → ℝ) (X : Boundary)
    (hX : X ∈ CubeBoundaryKernelL2.cutoff t) :
    inverseFunction t F (chords X t)=F X/Real.sqrt (weight t X) := by
  have hq : chords X t ∈ chordRegion := by
    simpa only [region,Set.mem_preimage,boundaryRay,reduced_axial] using (ray_region_iff X t).mpr hX
  unfold inverseFunction
  rw [Set.indicator_of_mem hq,coords_chords,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
  rfl

private theorem weighted_square (t : ℝ) (ht : 0 < t) (F : Boundary → ℝ) (X : Boundary) :
    t^15*(CubeBoundaryHaarL2.density (t • X)*(CubeBoundaryKernelL2.cutoff t).indicator
      (fun X => inverseFunction t F (chords X t)^2) X)=
      (CubeBoundaryKernelL2.cutoff t).indicator (fun X => F X^2) X := by
  classical
  by_cases hX : X ∈ CubeBoundaryKernelL2.cutoff t
  · rw [Set.indicator_of_mem hX,Set.indicator_of_mem hX,inverse_on_chart t ht F X hX,div_pow,
      Real.sq_sqrt (weight_positive t ht X).le]
    rw [← mul_assoc]
    change weight t X*(F X^2/weight t X)=F X^2
    field_simp [(weight_positive t ht X).ne']
  · rw [Set.indicator_of_notMem hX,Set.indicator_of_notMem hX]
    ring

theorem inverseFunction_memLp (t : ℝ) (ht : 0 < t) (F : EuclideanL2) :
    MemLp (inverseFunction t F) 2 chordHaar := by
  have hm := inverseFunction_measurable t F (Lp.stronglyMeasurable F).measurable
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hi := ((Lp.memLp F).integrable_sq.indicator (CubeBoundaryKernelL2.cutoff_measurable t)).div_const (t^15)
  have hs : Integrable (fun X : Boundary => CubeBoundaryHaarL2.density (t • X)*
      (CubeBoundaryKernelL2.cutoff t).indicator (fun X => inverseFunction t F (chords X t)^2) X) := by
    convert hi using 1
    funext X
    apply (eq_div_iff (pow_pos ht 15).ne').mpr
    nlinarith [weighted_square t ht F X]
  have hr := (scaled_local_integrable_iff (fun q => inverseFunction t F q^2)
    (hm.pow_const 2) t ht.ne').mpr hs
  have hh := (integrable_indicator_iff chordRegion_measurable).mpr hr
  convert hh using 1
  funext q
  classical
  by_cases hq : q ∈ chordRegion
  · rw [Set.indicator_of_mem hq]
  · rw [Set.indicator_of_notMem hq]
    simp only [inverseFunction,Set.indicator_of_notMem hq,zero_pow (by norm_num : (2:ℕ)≠0)]

def inverseClass (t : ℝ) (ht : 0 < t) (F : EuclideanL2) : ChordL2 :=
  (inverseFunction_memLp t ht F).toLp (inverseFunction t F)
theorem inverseClass_coe (t : ℝ) (ht : 0 < t) (F : EuclideanL2) :
    inverseClass t ht F =ᵐ[chordHaar] inverseFunction t F := MemLp.coeFn_toLp _

def cutoffClass (t : ℝ) (F : EuclideanL2) : EuclideanL2 :=
  ((Lp.memLp F).indicator (CubeBoundaryKernelL2.cutoff_measurable t)).toLp
    ((CubeBoundaryKernelL2.cutoff t).indicator F)
theorem cutoffClass_coe (t : ℝ) (F : EuclideanL2) :
    cutoffClass t F =ᵐ[volume] (CubeBoundaryKernelL2.cutoff t).indicator F := MemLp.coeFn_toLp _

theorem forward_inverseClass (t : ℝ) (ht : 0 < t) (F : EuclideanL2) :
    forward t ht (inverseClass t ht F)=cutoffClass t F := by
  apply Lp.ext
  filter_upwards [forward_coe t ht (inverseClass t ht F),cutoffClass_coe t F,
    scaled_ae_comp (inverseClass_coe t ht F) t ht.ne'] with X hV hC hI
  rw [hV,hC]
  classical
  by_cases hX : X ∈ CubeBoundaryKernelL2.cutoff t
  · simp only [pullback,Set.indicator_of_mem hX]
    change inverseClass t ht F (chords X t)=inverseFunction t F (chords X t) at hI
    rw [hI,inverse_on_chart t ht F X hX]
    change Real.sqrt (weight t X)*(F X/Real.sqrt (weight t X))=F X
    field_simp [(Real.sqrt_pos.mpr (weight_positive t ht X)).ne']
  · simp only [pullback,Set.indicator_of_notMem hX]

theorem local_inverseClass (t : ℝ) (ht : 0 < t) (F : EuclideanL2) :
    localClass (inverseClass t ht F)=inverseClass t ht F := by
  apply Lp.ext
  filter_upwards [localClass_coe (inverseClass t ht F),inverseClass_coe t ht F] with q hL hI
  rw [hL]
  classical
  by_cases hq : q ∈ chordRegion
  · rw [Set.indicator_of_mem hq]
  · rw [Set.indicator_of_notMem hq,hI]
    simp only [inverseFunction,Set.indicator_of_notMem hq]

theorem backward_cutoff (t : ℝ) (ht : 0 < t) (F : EuclideanL2) :
    backward t ht (cutoffClass t F)=backward t ht F := by
  apply ext_inner_right ℝ
  intro g
  change inner ℝ ((forward t ht).adjoint (cutoffClass t F)) g=inner ℝ ((forward t ht).adjoint F) g
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cutoffClass_coe t F,forward_coe t ht g] with X hC hV
  rw [hC,hV,Real.inner_apply,Real.inner_apply]
  classical
  by_cases hX : X ∈ CubeBoundaryKernelL2.cutoff t
  · rw [Set.indicator_of_mem hX]
  · simp only [Set.indicator_of_notMem hX,pullback,zero_mul,mul_zero]

/-- The explicit inverse-coordinate class is the ACTUAL adjoint for every Euclidean L2 input. -/
theorem inverseClass_eq_backward (t : ℝ) (ht : 0 < t) (F : EuclideanL2) :
    inverseClass t ht F=backward t ht F := by
  have h : backward t ht (cutoffClass t F)=inverseClass t ht F := by
    rw [← forward_inverseClass t ht F,backward_forward,local_inverseClass]
  exact h.symm.trans (backward_cutoff t ht F)

theorem backward_coe (t : ℝ) (ht : 0 < t) (F : EuclideanL2) :
    backward t ht F =ᵐ[chordHaar] inverseFunction t F := by
  rw [← inverseClass_eq_backward]
  exact inverseClass_coe t ht F

/-- The final projection is EXACTLY the entire Euclidean cutoff subspace. -/
theorem forward_backward (t : ℝ) (ht : 0 < t) (F : EuclideanL2) :
    forward t ht (backward t ht F)=cutoffClass t F := by
  rw [← inverseClass_eq_backward,forward_inverseClass]

end OperatorDerivativeRewrite.Foundation.CubeBoundaryChartInverse
