import Foundation.CubeBoundaryExterior

/-! Exact restricted Haar transport for the actual five boundary chords. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.CubeBoundaryChartMeasure
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open CubeAxialSlice CubeHaarSplit CubeChartAction CubeBoundaryExterior
open FourCubeHaarProductCoordinates (coordinateLaw coordinateLaw_finite chart_map_coordinateLaw
  chartDensity_nonneg chartDensity_measurable chartDensity_integrable coordinateLaw_apply_integral)

def chart (X : Boundary) : Chords := fun i => hemisphereChart (X i)
def jointHemisphere : Set Chords := Set.univ.pi (fun _ : Fin 5 => hemisphere)
def chartLaw : Measure Boundary := Measure.pi (fun _ : Fin 5 => coordinateLaw)
private instance chartLaw_finite : IsFiniteMeasure chartLaw := by unfold chartLaw; infer_instance

theorem chart_measurable : Measurable chart :=
  measurable_pi_iff.mpr (fun i => SU2HemisphereChart.chart_measurable.comp (measurable_pi_apply i))

theorem chart_map : chartLaw.map chart=chordHaar.restrict jointHemisphere := by
  rw [show chordHaar.restrict jointHemisphere=
    Measure.pi (fun _ : Fin 5 => law.restrict hemisphere) from
      Measure.restrict_pi_pi (fun _ : Fin 5 => law) (fun _ => hemisphere)]
  have h := Measure.pi_map_pi (fun _ : Fin 5 =>
    SU2HemisphereChart.chart_measurable.aemeasurable (μ := coordinateLaw))
  change (Measure.pi (fun _ : Fin 5 => coordinateLaw)).map chart=_
  rw [chart_map_coordinateLaw] at h
  exact h

theorem region_subset : chordRegion ⊆ jointHemisphere := by
  intro q hq i _
  exact (hq i).1

theorem cutoff_preimage : chart ⁻¹' chordRegion=CubeBoundaryKernelL2.cutoff 1 := by
  ext X
  simp [chart,chordRegion,CubeBoundaryKernelL2.cutoff,chart_mem_hemisphere,coordinates_chart]

theorem density_integrable : Integrable CubeBoundaryHaarL2.density := by
  rw [show CubeBoundaryHaarL2.density=(fun X : Boundary => ∏ i,chartDensity (X i)) from rfl,volume_pi]
  exact Integrable.fintype_prod (fun _ : Fin 5 => chartDensity_integrable)

private theorem integral_density_box (s : Fin 5 → Set Triple) (hs : ∀ i,MeasurableSet (s i)) :
    (∫ X in Set.univ.pi s,CubeBoundaryHaarL2.density X)=∏ i : Fin 5,∫ y in s i,chartDensity y := by
  have hi : (Set.univ.pi s).indicator CubeBoundaryHaarL2.density=
      (fun X : Boundary => ∏ i : Fin 5,(s i).indicator chartDensity (X i)) := by
    funext X
    by_cases hX : X ∈ Set.univ.pi s
    · have hx : ∀ i,X i ∈ s i := by simpa only [Set.mem_pi,Set.mem_univ,true_implies] using hX
      rw [Set.indicator_of_mem hX]
      unfold CubeBoundaryHaarL2.density
      apply Finset.prod_congr rfl
      intro i _
      exact (Set.indicator_of_mem (hx i) _).symm
    · rw [Set.indicator_of_notMem hX]
      have hx : ¬ ∀ i,X i ∈ s i := by simpa only [Set.mem_pi,Set.mem_univ,true_implies] using hX
      push_neg at hx
      obtain ⟨i,hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [← integral_indicator (MeasurableSet.univ_pi hs),hi,volume_pi,integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact integral_indicator (hs i)

theorem chartLaw_density : chartLaw=(volume : Measure Boundary).withDensity
    (fun X => ENNReal.ofReal (CubeBoundaryHaarL2.density X)) := by
  unfold chartLaw
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal density_integrable.integrableOn
      (ae_of_all _ (fun X => (CubeBoundaryHaarL2.density_positive X).le)),integral_density_box s hs,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun y => chartDensity_nonneg y))]
  apply Finset.prod_congr rfl
  intro i _
  exact (coordinateLaw_apply_integral (s i) (hs i)).symm

theorem integral_local (f : Chords → ℝ) (hf : Measurable f) :
    (∫ q in chordRegion,f q ∂chordHaar)=∫ X : Boundary,
      CubeBoundaryHaarL2.density X*chordRegion.indicator f (chart X) := by
  have h := integral_map (μ := chartLaw) chart_measurable.aemeasurable
    (hf.indicator chordRegion_measurable).aestronglyMeasurable
  rw [chart_map,integral_indicator chordRegion_measurable,
    Measure.restrict_restrict_of_subset region_subset] at h
  rw [chartLaw_density,integral_withDensity_eq_integral_toReal_smul
    CubeBoundaryHaarL2.density_continuous.measurable.ennreal_ofReal
      (ae_of_all volume (fun _ => ENNReal.ofReal_lt_top))] at h
  simpa only [ENNReal.toReal_ofReal (CubeBoundaryHaarL2.density_positive _).le,smul_eq_mul] using h

theorem local_integrable_iff (f : Chords → ℝ) (hf : Measurable f) :
    IntegrableOn f chordRegion chordHaar ↔ Integrable (fun X : Boundary =>
      CubeBoundaryHaarL2.density X*chordRegion.indicator f (chart X)) := by
  have hp : MeasurePreserving chart chartLaw (chordHaar.restrict jointHemisphere) :=
    ⟨chart_measurable,chart_map⟩
  have h := hp.integrable_comp (hf.indicator chordRegion_measurable).aestronglyMeasurable
  rw [integrable_indicator_iff chordRegion_measurable] at h
  simp only [IntegrableOn] at h
  rw [Measure.restrict_restrict_of_subset region_subset] at h
  rw [chartLaw_density,integrable_withDensity_iff_integrable_smul₀'
    CubeBoundaryHaarL2.density_continuous.measurable.ennreal_ofReal.aemeasurable
      (ae_of_all volume (fun _ => ENNReal.ofReal_lt_top))] at h
  simpa only [Function.comp_def,ENNReal.toReal_ofReal (CubeBoundaryHaarL2.density_positive _).le,
    smul_eq_mul,IntegrableOn] using h.symm

theorem field_finrank : Module.finrank ℝ Boundary=15 := by
  change Module.finrank ℝ (Fin 5 → Fin 3 → ℝ)=15
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fin_fun,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  norm_num

theorem integral_rescale (f : Boundary → ℝ) (t : ℝ) (ht : t ≠ 0) :
    (∫ X : Boundary,f X)=|t|^15*(∫ X : Boundary,f (t • X)) := by
  have h := Measure.integral_comp_smul (volume : Measure Boundary) f t
  rw [field_finrank,smul_eq_mul,abs_inv,abs_pow] at h
  rw [h]
  have hp : |t|^15 ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr ht)
  field_simp

theorem integral_local_scaled (f : Chords → ℝ) (hf : Measurable f) (t : ℝ) (ht : 0 < t) :
    (∫ q in chordRegion,f q ∂chordHaar)=t^15*(∫ X : Boundary,
      CubeBoundaryHaarL2.density (t • X)*
        (CubeBoundaryKernelL2.cutoff t).indicator (fun X => f (chords X t)) X) := by
  rw [integral_local f hf,integral_rescale _ t ht.ne',abs_of_pos ht]
  congr 1
  apply integral_congr_ae
  filter_upwards with X
  have he : chart (t • X)=chords X t := rfl
  have hm : chart (t • X) ∈ chordRegion ↔ X ∈ CubeBoundaryKernelL2.cutoff t := by
    rw [he]
    simpa only [CubeBoundaryExterior.region,Set.mem_preimage,boundaryRay,reduced_axial] using ray_region_iff X t
  classical
  by_cases hx : X ∈ CubeBoundaryKernelL2.cutoff t
  · rw [Set.indicator_of_mem (hm.mpr hx),Set.indicator_of_mem hx,he]
  · rw [Set.indicator_of_notMem (fun h => hx (hm.mp h)),Set.indicator_of_notMem hx]

theorem scaled_local_integrable_iff (f : Chords → ℝ) (hf : Measurable f) (t : ℝ) (ht : t ≠ 0) :
    IntegrableOn f chordRegion chordHaar ↔ Integrable (fun X : Boundary =>
      CubeBoundaryHaarL2.density (t • X)*
        (CubeBoundaryKernelL2.cutoff t).indicator (fun X => f (chords X t)) X) := by
  rw [local_integrable_iff f hf]
  have h := integrable_comp_smul_iff (volume : Measure Boundary)
    (fun X : Boundary => CubeBoundaryHaarL2.density X*chordRegion.indicator f (chart X)) ht
  rw [← h]
  suffices he : (fun X : Boundary => CubeBoundaryHaarL2.density (t • X)*
      chordRegion.indicator f (chart (t • X)))=
      (fun X : Boundary => CubeBoundaryHaarL2.density (t • X)*
        (CubeBoundaryKernelL2.cutoff t).indicator (fun X => f (chords X t)) X) by rw [he]
  funext X
  have hm : chart (t • X) ∈ chordRegion ↔ X ∈ CubeBoundaryKernelL2.cutoff t := by
    rw [show chart (t • X)=chords X t from rfl]
    simpa only [region,Set.mem_preimage,boundaryRay,reduced_axial] using ray_region_iff X t
  classical
  by_cases hx : X ∈ CubeBoundaryKernelL2.cutoff t
  · rw [Set.indicator_of_mem (hm.mpr hx),Set.indicator_of_mem hx]
    rfl
  · rw [Set.indicator_of_notMem (fun h => hx (hm.mp h)),Set.indicator_of_notMem hx]

/-- Positive chart density transports actual Haar null-set identities to Euclidean volume. -/
theorem chart_ae_comp {f g : Chords → ℝ} (hfg : f =ᵐ[chordHaar] g) :
    (fun X : Boundary => f (chart X)) =ᵐ[volume] (fun X => g (chart X)) := by
  have hp : MeasurePreserving chart chartLaw (chordHaar.restrict jointHemisphere) :=
    ⟨chart_measurable,chart_map⟩
  have h := hp.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hfg)
  rw [chartLaw_density] at h
  change (∀ᵐ X : Boundary ∂(volume : Measure Boundary).withDensity
    (fun X => ENNReal.ofReal (CubeBoundaryHaarL2.density X)), f (chart X)=g (chart X)) at h
  rw [ae_withDensity_iff CubeBoundaryHaarL2.density_continuous.measurable.ennreal_ofReal] at h
  filter_upwards [h] with X hX
  exact hX (ne_of_gt (ENNReal.ofReal_pos.mpr (CubeBoundaryHaarL2.density_positive X)))

theorem scaled_ae_comp {f g : Chords → ℝ} (hfg : f =ᵐ[chordHaar] g) (t : ℝ) (ht : t ≠ 0) :
    (fun X : Boundary => f (chords X t)) =ᵐ[volume] (fun X => g (chords X t)) := by
  have h := (Measure.quasiMeasurePreserving_smul (volume : Measure Boundary) ht).ae_eq_comp
    (chart_ae_comp hfg)
  exact h

end OperatorDerivativeRewrite.Foundation.CubeBoundaryChartMeasure
