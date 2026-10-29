import Foundation.FourCubeFullHaarCoordinates
import Foundation.FourCubeHaarLaplaceDensity

/-! Genuine integrable full32 Haar observables, exact cutoff rescaling and a
single integrable Gaussian majorant. No quadratic or odd integral limit is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullHaarCutoff
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open OneSidedBlockRank FourCubeHaarParity FourCubeFullChartOdd
open FourCubeFullHaarCoordinates

attribute [local irreducible] OneSidedBlockIncidence.edges

theorem integrable_joint_iff (f : InteriorState → ℝ) (hf : Measurable f) :
    IntegrableOn f jointHemisphere interiorHaar ↔
      Integrable (fun Y : Coordinates => productDensity Y*f (chartField Y)) := by
  have hm := integrable_map_measure (μ := productCoordinateLaw)
    (f := chartField) hf.aestronglyMeasurable chartField_measurable.aemeasurable
  rw [chartField_map] at hm
  have hd : Integrable (fun Y : Coordinates => f (chartField Y)) productCoordinateLaw ↔
      Integrable (fun Y : Coordinates => productDensity Y*f (chartField Y)) := by
    rw [productCoordinateLaw_density]
    have h := integrable_withDensity_iff_integrable_smul'
      productDensity_measurable.ennreal_ofReal
      (ae_of_all (volume : Measure Coordinates) (fun _ => ENNReal.ofReal_lt_top))
      (g := fun Y : Coordinates => f (chartField Y))
    simpa only [ENNReal.toReal_ofReal (productDensity_nonneg _),smul_eq_mul] using h
  exact hm.trans hd

/-- Both integrability and the actual real observable identity, on an explicit domain. -/
theorem observable_transport (f : InteriorState → ℝ) (hf : Measurable f)
    (hi : IntegrableOn f jointHemisphere interiorHaar) :
    Integrable (fun Y : Coordinates => productDensity Y*f (chartField Y)) ∧
      (∫ U in jointHemisphere,f U ∂interiorHaar)=
        ∫ Y : Coordinates,productDensity Y*f (chartField Y) := by
  refine ⟨(integrable_joint_iff f hf).mp hi,?_⟩
  calc
    _ = ∫ Y : Coordinates,f (chartField Y) ∂productCoordinateLaw := by
      rw [← chartField_map]
      exact integral_map chartField_measurable.aemeasurable hf.aestronglyMeasurable
    _ = _ := by
      rw [productCoordinateLaw_density]
      have h := integral_withDensity_eq_integral_toReal_smul
        productDensity_measurable.ennreal_ofReal
        (ae_of_all (volume : Measure Coordinates) (fun _ => ENNReal.ofReal_lt_top))
        (fun Y : Coordinates => f (chartField Y))
      simpa only [ENNReal.toReal_ofReal (productDensity_nonneg _),smul_eq_mul] using h

def physicalCutoff : Set InteriorState :=
  {U | ∀ e : Interior,0 < halfTrace (U e) ∧ chartRate (coordinates (U e)) ≤ 2}
def coordinateCutoff : Set Coordinates := {Y | ∀ e : Interior,chartRate (Y e) ≤ 2}

theorem physicalCutoff_measurable : MeasurableSet physicalCutoff := by
  have hR : Measurable chartRate := by unfold chartRate; fun_prop
  unfold physicalCutoff
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro e
  exact (measurableSet_lt measurable_const
    (QuaternionSU2Representation.halfTrace_measurable.comp (measurable_pi_apply e))).inter
      (measurableSet_le ((hR.comp coordinates_measurable).comp (measurable_pi_apply e))
        measurable_const)

theorem cutoff_subset_joint : physicalCutoff ⊆ jointHemisphere := by
  intro U hU e he
  exact (hU e).1

theorem cutoff_preimage : chartField ⁻¹' physicalCutoff=coordinateCutoff := by
  ext Y
  simp only [Set.mem_preimage,physicalCutoff,coordinateCutoff,Set.mem_setOf_eq,chartField,
    coordinates_chart,chart_halfTrace]
  constructor
  · intro h e
    exact (h e).2
  · intro h e
    exact ⟨inv_pos.mpr (radius_positive (Y e)),h e⟩

theorem coordinateCutoff_measurable : MeasurableSet coordinateCutoff := by
  rw [← cutoff_preimage]
  exact physicalCutoff_measurable.preimage chartField_measurable

/-- Exact cutoff law for arbitrary measurable observables integrable on that cutoff. -/
theorem cutoff_observable_transport (f : InteriorState → ℝ) (hf : Measurable f)
    (hi : IntegrableOn f physicalCutoff interiorHaar) :
    Integrable (coordinateCutoff.indicator (fun Y : Coordinates => productDensity Y*f (chartField Y))) ∧
      (∫ U in physicalCutoff,f U ∂interiorHaar)=
        ∫ Y in coordinateCutoff,productDensity Y*f (chartField Y) := by
  classical
  have hgi : Integrable (physicalCutoff.indicator f) interiorHaar :=
    (integrable_indicator_iff physicalCutoff_measurable).mpr hi
  obtain ⟨hI,hE⟩ := observable_transport (physicalCutoff.indicator f)
    (hf.indicator physicalCutoff_measurable) hgi.integrableOn
  have he : (fun Y : Coordinates => productDensity Y*(physicalCutoff.indicator f) (chartField Y))=
      coordinateCutoff.indicator (fun Y : Coordinates => productDensity Y*f (chartField Y)) := by
    funext Y
    have hh : chartField Y∈physicalCutoff ↔ Y∈coordinateCutoff := by
      change Y∈chartField ⁻¹' physicalCutoff ↔ _
      rw [cutoff_preimage]
    by_cases hY : Y∈coordinateCutoff
    · simp only [Set.indicator_of_mem hY,Set.indicator_of_mem (hh.mpr hY)]
    · simp only [Set.indicator_of_notMem hY,Set.indicator_of_notMem (mt hh.mp hY),mul_zero]
  rw [he] at hI hE
  rw [setIntegral_indicator physicalCutoff_measurable,Set.inter_eq_right.mpr cutoff_subset_joint,
    integral_indicator coordinateCutoff_measurable] at hE
  exact ⟨hI,hE⟩

def density (b : Fin 3 → SU2) (β : ℝ) : Coordinates → ℝ :=
  coordinateCutoff.indicator (fun Y => productDensity Y*FourCubeCompletedHaar.completedWeight β b (chartField Y))
def scaledDensity (b : Fin 3 → SU2) (β t : ℝ) (Y : Coordinates) : ℝ := density b β (t • Y)
def localPartition (b : Fin 3 → SU2) (β : ℝ) : ℝ :=
  ∫ U in physicalCutoff,FourCubeCompletedHaar.completedWeight β b U ∂interiorHaar

theorem density_integrable (b : Fin 3 → SU2) (β : ℝ) : Integrable (density b β) := by
  have hm : Measurable (FourCubeCompletedHaar.completedWeight β b) :=
    (measurable_const.mul (FourCubeCompletedHaar.completed_measurable b)).exp
  exact (cutoff_observable_transport _ hm (FourCubeCompletedHaar.completed_integrable β b).integrableOn).1

theorem scaledDensity_integrable (b : Fin 3 → SU2) (β t : ℝ) (ht : t≠0) :
    Integrable (scaledDensity b β t) := (density_integrable b β).comp_smul ht

/-- Actual full32 restricted-Haar partition with the correct96-dimensional Jacobian. -/
theorem localPartition_rescale (b : Fin 3 → SU2) (β t : ℝ) (ht : t≠0) :
    localPartition b β=|t|^96*(∫ Y : Coordinates,scaledDensity b β t Y) := by
  have hm : Measurable (FourCubeCompletedHaar.completedWeight β b) :=
    (measurable_const.mul (FourCubeCompletedHaar.completed_measurable b)).exp
  have h := (cutoff_observable_transport _ hm (FourCubeCompletedHaar.completed_integrable β b).integrableOn).2
  rw [← integral_indicator coordinateCutoff_measurable] at h
  change localPartition b β=∫ Y : Coordinates,density b β Y at h
  rw [h,integral_rescale (density b β) t ht]
  rfl

theorem productDensity_le_zero (Y : Coordinates) : productDensity Y ≤ productDensity 0 := by
  apply Finset.prod_le_prod₀
  · intro e he
    exact FourCubeHaarProductCoordinates.chartDensity_nonneg (Y e)
  · intro e he
    exact FourCubeHaarLaplaceDensity.chartDensity_le_zero (Y e)

theorem productDensity_continuous : Continuous productDensity := by
  exact continuous_finset_prod _ (fun e _ =>
    FourCubeHaarLaplaceDensity.chartDensity_continuous.comp (continuous_apply e))

theorem productDensity_positive (Y : Coordinates) : 0 < productDensity Y :=
  Finset.prod_pos (fun e _ => FourCubeHaarLaplaceDensity.chartDensity_positive (Y e))

theorem scaledDensity_nonneg (b : Fin 3 → SU2) (β t : ℝ) (Y : Coordinates) :
    0 ≤ scaledDensity b β t Y := by
  classical
  unfold scaledDensity density
  by_cases h : t • Y∈coordinateCutoff
  · rw [Set.indicator_of_mem h]
    exact mul_nonneg (productDensity_nonneg _) (Real.exp_pos _).le
  · rw [Set.indicator_of_notMem h]

theorem gaussian_majorant_integrable :
    Integrable (fun Y : Coordinates => Real.exp (-FourCubeFullChartDomination.mass Y/4)) := by
  have hi : Integrable (fun y : Triple => Real.exp (-(chartRate y-1)/4)) := by
    have hh := Integrable.fintype_prod (fun _ : Fin 3 =>
      integrable_exp_neg_mul_sq (b := (1/4 : ℝ)) (by norm_num))
    rw [volume_pi]
    convert hh using 1
    funext y
    rw [← Real.exp_sum]
    congr 1
    simp [chartRate,Fin.sum_univ_three]
    ring
  have he : (fun Y : Coordinates => Real.exp (-FourCubeFullChartDomination.mass Y/4))=
      (fun Y => ∏ e : Interior,Real.exp (-(chartRate (Y e)-1)/4)) := by
    funext Y
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.sum_div,Finset.sum_neg_distrib]
    rfl
  rw [he,volume_pi]
  exact Integrable.fintype_prod (fun _ : Interior => hi)

/-- One integrable majorant for the actual rescaled96-dimensional cutoff density. -/
theorem scaledDensity_bound (b : Fin 3 → SU2) (β t : ℝ)
    (hβ : 0 ≤ β) (ht : β*t^2=1) (Y : Coordinates) :
    scaledDensity b β t Y ≤ productDensity 0*Real.exp (-FourCubeFullChartDomination.mass Y/4) := by
  classical
  unfold scaledDensity density
  by_cases h : t • Y∈coordinateCutoff
  · rw [Set.indicator_of_mem h]
    have hh : ∀ e,chartRate (t • Y e) ≤ 2 := h
    have hw := FourCubeFullChartDomination.completed_weight_bound b β t hβ ht Y hh
    exact mul_le_mul (productDensity_le_zero _) hw (Real.exp_pos _).le (productDensity_nonneg _)
  · rw [Set.indicator_of_notMem h]
    exact mul_nonneg (productDensity_nonneg _) (Real.exp_pos _).le

theorem productDensity_zero : productDensity (0 : Coordinates)=(1/(2*Real.pi^2))^32 := by
  simp [productDensity,chartDensity,chartRate,OneSidedBlockIncidence.edges_card]

theorem productDensity_scaled_tendsto (Y : Coordinates) :
    Tendsto (fun t : ℝ => productDensity (t • Y)) (𝓝 0) (𝓝 ((1/(2*Real.pi^2))^32)) := by
  have hs : Continuous (fun t : ℝ => t • Y) := continuous_id.smul continuous_const
  have h := (productDensity_continuous.comp hs).tendsto (0 : ℝ)
  simpa only [Function.comp_def,zero_smul,productDensity_zero] using h

end OperatorDerivativeRewrite.Foundation.FourCubeFullHaarCutoff
