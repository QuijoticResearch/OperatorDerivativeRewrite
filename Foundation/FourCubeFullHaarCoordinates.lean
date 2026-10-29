import Foundation.FourCubeFullChartDomination
import Foundation.FourCubeHaarProductCoordinates

/-! Actual full32 restricted-Haar transport and96-dimensional chart scaling.
Reuse the verified one-link coordinate law; no pinned31 measure is identified with this one. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullHaarCoordinates
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open OneSidedBlockRank FourCubeHaarParity
open FourCubeFullChartOdd (Coordinates)
open FourCubeHaarProductCoordinates (coordinateLaw coordinateLaw_eq_map chart_map_coordinateLaw
  chartDensity_nonneg chartDensity_measurable chartDensity_integrable coordinateLaw_apply_integral)

attribute [local irreducible] OneSidedBlockIncidence.edges

def chartField (Y : Coordinates) : InteriorState := fun e => hemisphereChart (Y e)

def jointHemisphere : Set InteriorState := Set.univ.pi (fun _ : Interior => hemisphere)

def coordinateField (U : InteriorState) : Coordinates := fun e => coordinates (U e)

def productCoordinateLaw : Measure Coordinates := Measure.pi (fun _ : Interior => coordinateLaw)

instance productCoordinateLaw_finite : IsFiniteMeasure productCoordinateLaw := by
  unfold productCoordinateLaw
  infer_instance

theorem jointHemisphere_measurable : MeasurableSet jointHemisphere :=
  MeasurableSet.univ_pi (fun _ => hemisphere_measurable)

theorem coordinateField_measurable : Measurable coordinateField :=
  measurable_pi_iff.mpr (fun e => coordinates_measurable.comp (measurable_pi_apply e))

theorem chartField_measurable : Measurable chartField :=
  measurable_pi_iff.mpr (fun e => chart_measurable.comp (measurable_pi_apply e))

theorem joint_restriction : interiorHaar.restrict jointHemisphere=
    Measure.pi (fun _ : Interior => QuaternionSU2Representation.law.restrict hemisphere) :=
  Measure.restrict_pi_pi (fun _ : Interior => QuaternionSU2Representation.law) (fun _ => hemisphere)

theorem coordinateField_map : (interiorHaar.restrict jointHemisphere).map coordinateField=
    productCoordinateLaw := by
  rw [joint_restriction]
  have hh := Measure.pi_map_pi (fun _ : Interior => coordinates_measurable.aemeasurable
    (μ := QuaternionSU2Representation.law.restrict hemisphere))
  change _=Measure.pi (fun _ : Interior => coordinateLaw)
  rw [← coordinateLaw_eq_map] at hh
  exact hh

theorem chartField_map : productCoordinateLaw.map chartField=
    interiorHaar.restrict jointHemisphere := by
  rw [joint_restriction]
  have hh := Measure.pi_map_pi (fun _ : Interior => chart_measurable.aemeasurable (μ := coordinateLaw))
  change (Measure.pi (fun _ : Interior => coordinateLaw)).map chartField=_
  rw [chart_map_coordinateLaw] at hh
  exact hh

theorem lintegral_joint_chart (f : InteriorState → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ U in jointHemisphere,f U ∂interiorHaar)=
      ∫⁻ Y : Coordinates,f (chartField Y) ∂productCoordinateLaw := by
  rw [← chartField_map,lintegral_map hf chartField_measurable]

def productDensity (Y : Coordinates) : ℝ := ∏ e : Interior,chartDensity (Y e)

theorem productDensity_nonneg (Y : Coordinates) : 0 ≤ productDensity Y :=
  Finset.prod_nonneg (fun e _ => chartDensity_nonneg (Y e))

theorem productDensity_measurable : Measurable productDensity := by
  unfold productDensity
  apply Finset.measurable_prod
  intro e _
  exact chartDensity_measurable.comp (measurable_pi_apply e)

theorem productDensity_integrable : Integrable productDensity := by
  rw [show productDensity=(fun Y : Coordinates => ∏ e : Interior,chartDensity (Y e)) from rfl,volume_pi]
  exact Integrable.fintype_prod (fun _ : Interior => chartDensity_integrable)

private theorem integral_productDensity_box (s : Interior → Set Triple) (hs : ∀ e,MeasurableSet (s e)) :
    (∫ Y in Set.univ.pi s,productDensity Y)=∏ e : Interior,∫ y in s e,chartDensity y := by
  have hi : (Set.univ.pi s).indicator productDensity=
      (fun Y : Coordinates => ∏ e : Interior,(s e).indicator chartDensity (Y e)) := by
    funext Y
    by_cases hY : Y∈Set.univ.pi s
    · have hy : ∀ e,Y e∈s e := by simpa only [Set.mem_pi,Set.mem_univ,true_implies] using hY
      rw [Set.indicator_of_mem hY]
      unfold productDensity
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

theorem productCoordinateLaw_density : productCoordinateLaw=
    (volume : Measure Coordinates).withDensity (fun Y => ENNReal.ofReal (productDensity Y)) := by
  unfold productCoordinateLaw
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal productDensity_integrable.integrableOn
      (ae_of_all _ productDensity_nonneg),integral_productDensity_box s hs,
    ENNReal.ofReal_prod_of_nonneg (fun e _ => integral_nonneg (fun y => chartDensity_nonneg y))]
  apply Finset.prod_congr rfl
  intro e _
  exact (coordinateLaw_apply_integral (s e) (hs e)).symm

theorem lintegral_joint_density (f : InteriorState → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ U in jointHemisphere,f U ∂interiorHaar)=
      ∫⁻ Y : Coordinates,ENNReal.ofReal (productDensity Y)*f (chartField Y) := by
  rw [lintegral_joint_chart f hf,productCoordinateLaw_density]
  exact lintegral_withDensity_eq_lintegral_mul (volume : Measure Coordinates)
    productDensity_measurable.ennreal_ofReal (hf.comp chartField_measurable)

theorem field_finrank : Module.finrank ℝ Coordinates=96 := by
  change Module.finrank ℝ (Interior → Fin 3 → ℝ)=96
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fin_fun,Finset.sum_const,Finset.card_univ,
    OneSidedBlockRank.interior_card]
  norm_num

theorem integral_rescale (f : Coordinates → ℝ) (t : ℝ) (ht : t ≠ 0) :
    (∫ Y : Coordinates,f Y)=|t|^96*(∫ Y : Coordinates,f (t • Y)) := by
  have hh := Measure.integral_comp_smul (volume : Measure Coordinates) f t
  rw [field_finrank,smul_eq_mul,abs_inv,abs_pow] at hh
  rw [hh]
  have hp : |t|^96 ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr ht)
  field_simp


end OperatorDerivativeRewrite.Foundation.FourCubeFullHaarCoordinates
