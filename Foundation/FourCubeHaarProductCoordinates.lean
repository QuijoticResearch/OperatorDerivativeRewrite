import Foundation.SU2HemisphereChart
import Foundation.FourCubeHemisphereCoercivity
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact joint restricted-Haar transport for the actual31 retained links. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.FourCubeHaarProductCoordinates
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open FourCubePinnedHaar FourCubeHemisphereCoercivity
open OneSidedPinnedInterior (Free)

def coordinateLaw : Measure Triple :=
  (volume : Measure Triple).withDensity (fun y => ENNReal.ofReal (chartDensity y))

theorem chartDensity_nonneg (y : Triple) : 0 ≤ chartDensity y := by
  unfold chartDensity
  positivity

theorem chartDensity_measurable : Measurable chartDensity := by
  unfold chartDensity chartRate
  fun_prop

theorem coordinateLaw_eq_map : coordinateLaw=
    (QuaternionSU2Representation.law.restrict hemisphere).map coordinates := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg coordinates_measurable]
  rw [coordinateLaw,lintegral_withDensity_eq_lintegral_mul _ chartDensity_measurable.ennreal_ofReal hg]
  exact (lintegral_coordinate_observable g hg).symm

instance coordinateLaw_finite : IsFiniteMeasure coordinateLaw := by
  rw [coordinateLaw_eq_map]
  infer_instance

theorem chart_map_coordinateLaw : coordinateLaw.map hemisphereChart=
    QuaternionSU2Representation.law.restrict hemisphere := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf chart_measurable]
  rw [coordinateLaw]
  have hh := lintegral_withDensity_eq_lintegral_mul (volume : Measure Triple)
    chartDensity_measurable.ennreal_ofReal (hf.comp chart_measurable)
  exact hh.trans (lintegral_haar_hemisphere_chart f hf).symm

def jointHemisphere : Set PinnedState := Set.univ.pi (fun _ : Free => hemisphere)

def coordinateField (U : PinnedState) : Field := fun e => coordinates (U e)

def productCoordinateLaw : Measure Field := Measure.pi (fun _ : Free => coordinateLaw)

instance productCoordinateLaw_finite : IsFiniteMeasure productCoordinateLaw := by
  unfold productCoordinateLaw
  infer_instance

theorem jointHemisphere_measurable : MeasurableSet jointHemisphere :=
  MeasurableSet.univ_pi (fun _ => hemisphere_measurable)

theorem coordinateField_measurable : Measurable coordinateField :=
  measurable_pi_iff.mpr (fun e => coordinates_measurable.comp (measurable_pi_apply e))

theorem chartField_measurable : Measurable chartField :=
  measurable_pi_iff.mpr (fun e => chart_measurable.comp (measurable_pi_apply e))

theorem joint_restriction : pinnedHaar.restrict jointHemisphere=
    Measure.pi (fun _ : Free => QuaternionSU2Representation.law.restrict hemisphere) :=
  Measure.restrict_pi_pi (fun _ : Free => QuaternionSU2Representation.law) (fun _ => hemisphere)

theorem coordinateField_map : (pinnedHaar.restrict jointHemisphere).map coordinateField=
    productCoordinateLaw := by
  rw [joint_restriction]
  have hh := Measure.pi_map_pi (fun _ : Free => coordinates_measurable.aemeasurable
    (μ := QuaternionSU2Representation.law.restrict hemisphere))
  change _=Measure.pi (fun _ : Free => coordinateLaw)
  rw [← coordinateLaw_eq_map] at hh
  exact hh

theorem chartField_map : productCoordinateLaw.map chartField=
    pinnedHaar.restrict jointHemisphere := by
  rw [joint_restriction]
  have hh := Measure.pi_map_pi (fun _ : Free => chart_measurable.aemeasurable (μ := coordinateLaw))
  change (Measure.pi (fun _ : Free => coordinateLaw)).map chartField=_
  rw [chart_map_coordinateLaw] at hh
  exact hh

theorem lintegral_joint_chart (f : PinnedState → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ U in jointHemisphere,f U ∂pinnedHaar)=
      ∫⁻ Y : Field,f (chartField Y) ∂productCoordinateLaw := by
  rw [← chartField_map,lintegral_map hf chartField_measurable]

theorem cutoff_preimage : chartField ⁻¹' localStateDomain=
    {Y : Field | ∀ e : Free,chartRate (Y e) ≤ 2} := by
  ext Y
  simp only [Set.mem_preimage,localStateDomain,Set.mem_setOf_eq,chartField,
    coordinates_chart,chart_halfTrace]
  constructor
  · intro h e
    exact (h e).2
  · intro h e
    exact ⟨inv_pos.mpr (radius_positive (Y e)),h e⟩


theorem chartDensity_integrable : Integrable chartDensity := by
  refine ⟨chartDensity_measurable.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ chartDensity_nonneg)).mpr
  have hh : coordinateLaw Set.univ < ∞ := measure_lt_top _ _
  simpa [coordinateLaw,withDensity_apply] using hh

def productDensity (Y : Field) : ℝ := ∏ e : Free,chartDensity (Y e)

theorem productDensity_nonneg (Y : Field) : 0 ≤ productDensity Y :=
  Finset.prod_nonneg (fun e _ => chartDensity_nonneg (Y e))

theorem productDensity_measurable : Measurable productDensity := by
  unfold productDensity
  apply Finset.measurable_prod
  intro e _
  exact chartDensity_measurable.comp (measurable_pi_apply e)

theorem productDensity_integrable : Integrable productDensity := by
  rw [show productDensity=(fun Y : Field => ∏ e : Free,chartDensity (Y e)) from rfl,volume_pi]
  exact Integrable.fintype_prod (fun _ : Free => chartDensity_integrable)

theorem coordinateLaw_apply_integral (s : Set Triple) (hs : MeasurableSet s) :
    coordinateLaw s=ENNReal.ofReal (∫ y in s,chartDensity y) := by
  rw [coordinateLaw,withDensity_apply _ hs]
  exact (ofReal_integral_eq_lintegral_ofReal chartDensity_integrable.integrableOn
    (ae_of_all _ chartDensity_nonneg)).symm

private theorem integral_productDensity_box (s : Free → Set Triple) (hs : ∀ e,MeasurableSet (s e)) :
    (∫ Y in Set.univ.pi s,productDensity Y)=∏ e : Free,∫ y in s e,chartDensity y := by
  have hi : (Set.univ.pi s).indicator productDensity=
      (fun Y : Field => ∏ e : Free,(s e).indicator chartDensity (Y e)) := by
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
    (volume : Measure Field).withDensity (fun Y => ENNReal.ofReal (productDensity Y)) := by
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

theorem lintegral_joint_density (f : PinnedState → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ U in jointHemisphere,f U ∂pinnedHaar)=
      ∫⁻ Y : Field,ENNReal.ofReal (productDensity Y)*f (chartField Y) := by
  rw [lintegral_joint_chart f hf,productCoordinateLaw_density]
  exact lintegral_withDensity_eq_lintegral_mul (volume : Measure Field)
    productDensity_measurable.ennreal_ofReal (hf.comp chartField_measurable)

theorem field_finrank : Module.finrank ℝ Field=93 := by
  change Module.finrank ℝ (Free → Fin 3 → ℝ)=93
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fin_fun,Finset.sum_const,Finset.card_univ,
    OneSidedPinnedInterior.free_card]
  norm_num

theorem integral_rescale (f : Field → ℝ) (t : ℝ) (ht : t ≠ 0) :
    (∫ Y : Field,f Y)=|t|^93*(∫ Y : Field,f (t • Y)) := by
  have hh := Measure.integral_comp_smul (volume : Measure Field) f t
  rw [field_finrank,smul_eq_mul,abs_inv,abs_pow] at hh
  rw [hh]
  have hp : |t|^93 ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr ht)
  field_simp

end OperatorDerivativeRewrite.Foundation.FourCubeHaarProductCoordinates
