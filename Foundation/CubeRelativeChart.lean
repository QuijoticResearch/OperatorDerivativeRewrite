import Foundation.CubeTemporalExterior

/-! Actual seven-relative-link Haar chart, with its exact 21-dimensional density. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.CubeRelativeChart
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open CubeTemporalRootHaar SU2HaarLaplaceUpper
open FourCubeHaarProductCoordinates (coordinateLaw coordinateLaw_finite chart_map_coordinateLaw
  chartDensity_nonneg chartDensity_measurable chartDensity_integrable coordinateLaw_apply_integral)

abbrev Field := RelativeIndex → Triple

def chartField (Y : Field) : Relative := fun v => hemisphereChart (Y v)
def jointHemisphere : Set Relative := Set.univ.pi (fun _ => hemisphere)
def localField : Set Relative := Set.univ.pi (fun _ => localCut)
def chartLaw : Measure Field := Measure.pi (fun _ : RelativeIndex => coordinateLaw)
private instance chartLaw_finite : IsFiniteMeasure chartLaw := by unfold chartLaw; infer_instance

theorem chartField_measurable : Measurable chartField :=
  measurable_pi_iff.mpr (fun v => chart_measurable.comp (measurable_pi_apply v))
theorem localField_measurable : MeasurableSet localField :=
  MeasurableSet.univ_pi (fun _ => localCut_measurable)
theorem localField_subset : localField ⊆ jointHemisphere := by
  intro h hh v hv
  exact localCut_subset (hh v hv)

theorem chartField_map : chartLaw.map chartField=relativeHaar.restrict jointHemisphere := by
  rw [show relativeHaar.restrict jointHemisphere=
    Measure.pi (fun _ : RelativeIndex => law.restrict hemisphere) from
    Measure.restrict_pi_pi (fun _ : RelativeIndex => law) (fun _ => hemisphere)]
  have hh := Measure.pi_map_pi (fun _ : RelativeIndex => chart_measurable.aemeasurable (μ := coordinateLaw))
  change (Measure.pi (fun _ : RelativeIndex => coordinateLaw)).map chartField=_
  rw [chart_map_coordinateLaw] at hh
  exact hh

def density (Y : Field) : ℝ := ∏ v,chartDensity (Y v)
theorem density_nonneg (Y : Field) : 0 ≤ density Y :=
  Finset.prod_nonneg (fun v _ => chartDensity_nonneg (Y v))
theorem density_measurable : Measurable density := by
  unfold density
  exact Finset.measurable_prod _ (fun v _ => chartDensity_measurable.comp (measurable_pi_apply v))
theorem density_integrable : Integrable density := by
  rw [show density=(fun Y : Field => ∏ v,chartDensity (Y v)) from rfl,volume_pi]
  exact Integrable.fintype_prod (fun _ : RelativeIndex => chartDensity_integrable)

private theorem integral_density_box (s : RelativeIndex → Set Triple) (hs : ∀ e,MeasurableSet (s e)) :
    (∫ Y in Set.univ.pi s,density Y)=∏ e : RelativeIndex,∫ y in s e,chartDensity y := by
  have hi : (Set.univ.pi s).indicator density=
      (fun Y : Field => ∏ e : RelativeIndex,(s e).indicator chartDensity (Y e)) := by
    funext Y
    by_cases hY : Y∈Set.univ.pi s
    · have hy : ∀ e,Y e∈s e := by simpa only [Set.mem_pi,Set.mem_univ,true_implies] using hY
      rw [Set.indicator_of_mem hY]
      unfold density
      apply Finset.prod_congr rfl
      intro e _
      exact (Set.indicator_of_mem (hy e) _).symm
    · rw [Set.indicator_of_notMem hY]
      have hy : ¬ ∀ e,Y e∈s e := by simpa only [Set.mem_pi,Set.mem_univ,true_implies] using hY
      push_neg at hy
      obtain ⟨e,he⟩ := hy
      exact (Finset.prod_eq_zero (Finset.mem_univ e) (Set.indicator_of_notMem he _)).symm
  rw [← integral_indicator (MeasurableSet.univ_pi hs),hi,volume_pi,
    integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro e _
  exact integral_indicator (hs e)

theorem chartLaw_density : chartLaw=
    (volume : Measure Field).withDensity (fun Y => ENNReal.ofReal (density Y)) := by
  unfold chartLaw
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal density_integrable.integrableOn
      (ae_of_all _ density_nonneg),integral_density_box s hs,
    ENNReal.ofReal_prod_of_nonneg (fun e _ => integral_nonneg (fun y => chartDensity_nonneg y))]
  apply Finset.prod_congr rfl
  intro e _
  exact (coordinateLaw_apply_integral (s e) (hs e)).symm


/-- Exact actual local Haar integral, with every cutoff and density factor retained. -/
theorem integral_local (f : Relative → ℝ) (hf : Measurable f) :
    (∫ h in localField,f h ∂relativeHaar)=
      ∫ Y : Field,density Y*localField.indicator f (chartField Y) := by
  classical
  have hm := hf.indicator localField_measurable
  have h := integral_map (μ := chartLaw) chartField_measurable.aemeasurable hm.aestronglyMeasurable
  rw [chartField_map,integral_indicator localField_measurable,
    Measure.restrict_restrict_of_subset localField_subset] at h
  rw [chartLaw_density,integral_withDensity_eq_integral_toReal_smul
    density_measurable.ennreal_ofReal (ae_of_all volume (fun _ => ENNReal.ofReal_lt_top))] at h
  simpa only [ENNReal.toReal_ofReal (density_nonneg _),smul_eq_mul] using h

theorem field_finrank : Module.finrank ℝ Field=21 := by
  change Module.finrank ℝ (RelativeIndex → Fin 3 → ℝ)=21
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fin_fun,Finset.sum_const,Finset.card_univ,relative_count]
  norm_num

theorem integral_rescale (f : Field → ℝ) (t : ℝ) (ht : t ≠ 0) :
    (∫ Y : Field,f Y)=|t|^21*(∫ Y : Field,f (t • Y)) := by
  have hh := Measure.integral_comp_smul (volume : Measure Field) f t
  rw [field_finrank,smul_eq_mul,abs_inv,abs_pow] at hh
  rw [hh]
  have hp : |t|^21 ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr ht)
  field_simp

end OperatorDerivativeRewrite.Foundation.CubeRelativeChart
