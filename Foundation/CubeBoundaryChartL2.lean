import Foundation.CubeBoundaryChartMeasure

/-! A genuine bounded half-density chart map on the whole five-chord L2 space.
Its norm is the original local mass, so it is not falsely declared unitary on all inputs. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.CubeBoundaryChartL2
open CubeChartAction CubeAxialSlice CubeHaarSplit CubeChordOperator CubeBoundaryExterior
open CubeBoundaryChartMeasure

abbrev EuclideanL2 := Lp ℝ 2 (volume : Measure Boundary)

def pullback (t : ℝ) (f : Chords → ℝ) (X : Boundary) : ℝ :=
  (CubeBoundaryKernelL2.cutoff t).indicator
    (fun X => Real.sqrt (t^15*CubeBoundaryHaarL2.density (t • X))*f (chords X t)) X

theorem pullback_measurable (t : ℝ) (f : Chords → ℝ) (hf : Measurable f) :
    Measurable (pullback t f) := by
  have hc : Measurable (fun X : Boundary => chords X t) :=
    chart_measurable.comp (measurable_const_smul t)
  have hd : Continuous (fun X : Boundary => Real.sqrt (t^15*CubeBoundaryHaarL2.density (t • X))) :=
    (continuous_const.mul (CubeBoundaryHaarL2.density_continuous.comp (continuous_const_smul t))).sqrt
  exact (hd.measurable.mul (hf.comp hc)).indicator (CubeBoundaryKernelL2.cutoff_measurable t)

theorem pullback_sq (t : ℝ) (ht : 0 < t) (f : Chords → ℝ) (X : Boundary) :
    (pullback t f X)^2=t^15*(CubeBoundaryHaarL2.density (t • X)*
      (CubeBoundaryKernelL2.cutoff t).indicator (fun X => f (chords X t)^2) X) := by
  classical
  unfold pullback
  by_cases hx : X ∈ CubeBoundaryKernelL2.cutoff t
  · rw [Set.indicator_of_mem hx,Set.indicator_of_mem hx,mul_pow,
      Real.sq_sqrt (mul_nonneg (pow_pos ht 15).le (CubeBoundaryHaarL2.density_positive _).le)]
    ring
  · rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem hx]
    ring

theorem pullback_memLp (t : ℝ) (ht : 0 < t) (f : ChordL2) : MemLp (pullback t f) 2 volume := by
  apply (memLp_two_iff_integrable_sq (pullback_measurable t f (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable).mpr
  have hi := ((scaled_local_integrable_iff (fun q => f q^2)
    ((Lp.stronglyMeasurable f).measurable.pow_const 2) t ht.ne').mp
      (Lp.memLp f).integrable_sq.integrableOn).const_mul (t^15)
  convert hi using 1
  funext X
  exact pullback_sq t ht f X

def forwardClass (t : ℝ) (ht : 0 < t) (f : ChordL2) : EuclideanL2 :=
  (pullback_memLp t ht f).toLp (pullback t f)

theorem forwardClass_coe (t : ℝ) (ht : 0 < t) (f : ChordL2) :
    forwardClass t ht f =ᵐ[volume] pullback t f := MemLp.coeFn_toLp _

/-- Exact original local mass; the t^15 Jacobian is included in the half-density. -/
theorem forwardClass_norm_sq (t : ℝ) (ht : 0 < t) (f : ChordL2) :
    ‖forwardClass t ht f‖^2=∫ q in chordRegion,f q^2 ∂chordHaar := by
  rw [BochnerL2Dominated.norm_sq_integral]
  calc
    _ = ∫ X : Boundary,(pullback t f X)^2 := by
      apply integral_congr_ae
      filter_upwards [forwardClass_coe t ht f] with X hX
      rw [hX,Real.norm_eq_abs,sq_abs]
    _ = _ := by
      simp_rw [pullback_sq t ht]
      rw [integral_const_mul]
      exact (integral_local_scaled (fun q => f q^2)
        ((Lp.stronglyMeasurable f).measurable.pow_const 2) t ht).symm

theorem forwardClass_contraction (t : ℝ) (ht : 0 < t) (f : ChordL2) :
    ‖forwardClass t ht f‖ ≤ ‖f‖ := by
  have h := setIntegral_le_integral (s := chordRegion) (Lp.memLp f).integrable_sq
    (ae_of_all _ (fun q => sq_nonneg (f q)))
  have hN : ‖f‖^2=∫ q,f q^2 ∂chordHaar := by
    simpa only [Real.norm_eq_abs,sq_abs] using BochnerL2Dominated.norm_sq_integral f
  rw [← forwardClass_norm_sq t ht f,← hN] at h
  nlinarith [norm_nonneg (forwardClass t ht f),norm_nonneg f]

theorem forwardClass_add (t : ℝ) (ht : 0 < t) (f g : ChordL2) :
    forwardClass t ht (f+g)=forwardClass t ht f+forwardClass t ht g := by
  apply Lp.ext
  filter_upwards [forwardClass_coe t ht (f+g),forwardClass_coe t ht f,forwardClass_coe t ht g,
    Lp.coeFn_add (forwardClass t ht f) (forwardClass t ht g),
    scaled_ae_comp (Lp.coeFn_add f g) t ht.ne'] with X h hF hG hA hfg
  rw [h,hA]
  simp only [Pi.add_apply]
  rw [hF,hG]
  classical
  by_cases hx : X ∈ CubeBoundaryKernelL2.cutoff t
  · simp only [pullback,Set.indicator_of_mem hx]
    change (f+g) (chords X t)=f (chords X t)+g (chords X t) at hfg
    rw [hfg]
    ring
  · simp only [pullback,Set.indicator_of_notMem hx,add_zero]

theorem forwardClass_smul (t : ℝ) (ht : 0 < t) (c : ℝ) (f : ChordL2) :
    forwardClass t ht (c • f)=c • forwardClass t ht f := by
  apply Lp.ext
  filter_upwards [forwardClass_coe t ht (c • f),forwardClass_coe t ht f,
    Lp.coeFn_smul c (forwardClass t ht f),scaled_ae_comp (Lp.coeFn_smul c f) t ht.ne'] with X h hF hS hcf
  rw [h,hS]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hF]
  classical
  by_cases hx : X ∈ CubeBoundaryKernelL2.cutoff t
  · simp only [pullback,Set.indicator_of_mem hx]
    change (c • f) (chords X t)=c*f (chords X t) at hcf
    rw [hcf]
    ring
  · simp only [pullback,Set.indicator_of_notMem hx,mul_zero]

def forward (t : ℝ) (ht : 0 < t) : ChordL2 →L[ℝ] EuclideanL2 :=
  ({toFun := forwardClass t ht
    map_add' := forwardClass_add t ht
    map_smul' := forwardClass_smul t ht} : ChordL2 →ₗ[ℝ] EuclideanL2).mkContinuous 1
      (fun f => by
        change ‖forwardClass t ht f‖ ≤ 1*‖f‖
        simpa only [one_mul] using forwardClass_contraction t ht f)

theorem forward_coe (t : ℝ) (ht : 0 < t) (f : ChordL2) :
    forward t ht f =ᵐ[volume] pullback t f := forwardClass_coe t ht f

theorem forward_norm_sq (t : ℝ) (ht : 0 < t) (f : ChordL2) :
    ‖forward t ht f‖^2=∫ q in chordRegion,f q^2 ∂chordHaar := forwardClass_norm_sq t ht f

theorem forward_contraction (t : ℝ) (ht : 0 < t) (f : ChordL2) :
    ‖forward t ht f‖ ≤ ‖f‖ := forwardClass_contraction t ht f

def backward (t : ℝ) (ht : 0 < t) : EuclideanL2 →L[ℝ] ChordL2 := (forward t ht).adjoint

private theorem pullback_mul (t : ℝ) (ht : 0 < t) (f g : Chords → ℝ) (X : Boundary) :
    pullback t f X*pullback t g X=t^15*(CubeBoundaryHaarL2.density (t • X)*
      (CubeBoundaryKernelL2.cutoff t).indicator (fun X => f (chords X t)*g (chords X t)) X) := by
  classical
  by_cases hx : X ∈ CubeBoundaryKernelL2.cutoff t
  · simp only [pullback,Set.indicator_of_mem hx]
    have hs := Real.sq_sqrt (mul_nonneg (pow_pos ht 15).le (CubeBoundaryHaarL2.density_positive (t • X)).le)
    calc
      _ = (Real.sqrt (t^15*CubeBoundaryHaarL2.density (t • X)))^2*
          (f (chords X t)*g (chords X t)) := by ring
      _ = _ := by rw [hs]; ring
  · simp only [pullback,Set.indicator_of_notMem hx,mul_zero,zero_mul]

theorem forward_inner (t : ℝ) (ht : 0 < t) (f g : ChordL2) :
    inner ℝ (forward t ht f) (forward t ht g)=∫ q in chordRegion,f q*g q ∂chordHaar := by
  rw [L2.inner_def]
  calc
    _ = ∫ X : Boundary,pullback t f X*pullback t g X := by
      apply integral_congr_ae
      filter_upwards [forward_coe t ht f,forward_coe t ht g] with X hF hG
      rw [hF,hG,Real.inner_apply]
    _ = _ := by
      simp_rw [pullback_mul t ht]
      rw [integral_const_mul]
      exact (integral_local_scaled (fun q => f q*g q)
        ((Lp.stronglyMeasurable f).measurable.mul (Lp.stronglyMeasurable g).measurable) t ht).symm

def localClass (f : ChordL2) : ChordL2 :=
  ((Lp.memLp f).indicator chordRegion_measurable).toLp (chordRegion.indicator f)

theorem localClass_coe (f : ChordL2) : localClass f =ᵐ[chordHaar] chordRegion.indicator f :=
  MemLp.coeFn_toLp _

/-- The initial projection is the ORIGINAL local-chord cutoff on the whole Haar L2 domain. -/
theorem backward_forward (t : ℝ) (ht : 0 < t) (f : ChordL2) :
    backward t ht (forward t ht f)=localClass f := by
  apply ext_inner_right ℝ
  intro g
  change inner ℝ ((forward t ht).adjoint (forward t ht f)) g=inner ℝ (localClass f) g
  rw [ContinuousLinearMap.adjoint_inner_left,forward_inner,L2.inner_def,
    ← integral_indicator chordRegion_measurable]
  apply integral_congr_ae
  filter_upwards [localClass_coe f] with q hq
  rw [hq,Real.inner_apply]
  classical
  by_cases h : q ∈ chordRegion
  · simp only [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h,zero_mul]

theorem forward_localClass (t : ℝ) (ht : 0 < t) (f : ChordL2) :
    forward t ht (localClass f)=forward t ht f := by
  apply Lp.ext
  filter_upwards [forward_coe t ht (localClass f),forward_coe t ht f,
    scaled_ae_comp (localClass_coe f) t ht.ne'] with X hL hF hq
  rw [hL,hF]
  classical
  by_cases hx : X ∈ CubeBoundaryKernelL2.cutoff t
  · have hm : chords X t ∈ chordRegion := by
      simpa only [region,Set.mem_preimage,boundaryRay,reduced_axial] using (ray_region_iff X t).mpr hx
    simp only [pullback,Set.indicator_of_mem hx]
    change localClass f (chords X t)=chordRegion.indicator (fun q => f q) (chords X t) at hq
    rw [hq,Set.indicator_of_mem hm]
  · simp only [pullback,Set.indicator_of_notMem hx]

/-- Exact partial-isometry identity. No surjectivity onto all Euclidean L2 is asserted. -/
theorem partial_isometry (t : ℝ) (ht : 0 < t) :
    (forward t ht).comp ((backward t ht).comp (forward t ht))=forward t ht := by
  apply ContinuousLinearMap.ext
  intro f
  change forward t ht (backward t ht (forward t ht f))=forward t ht f
  rw [backward_forward,forward_localClass]

end OperatorDerivativeRewrite.Foundation.CubeBoundaryChartL2
