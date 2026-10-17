import Foundation.StickyObservedClock
import Foundation.AmbientNullAugmentation
import Mathlib.Probability.Process.Adapted

/-! Causal recovery of the operational clock in the actual sticky process's
own natural filtration, with explicit ambient null augmentation. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyNaturalClock
open InfiniteGaussian BrownianMassRandomTimeChange StickyObservedClock
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath
  BrownianMassRandomTimeChange.inverse BrownianRandomMassClock.mass

def naturalPast (κ : ℝ≥0) : Filtration ℝ≥0 (inferInstance : MeasurableSpace SampleSpace) :=
  Filtration.natural (fun t ω => changedPath κ ω t)
    (fun t => (changedPath_coordinate_measurable κ t).stronglyMeasurable)

theorem state_stronglyAdapted (κ : ℝ≥0) :
    StronglyAdapted (naturalPast κ) (fun t ω => changedPath κ ω t) :=
  Filtration.stronglyAdapted_natural _

def augmentedNaturalPast (κ : ℝ≥0) : Filtration ℝ≥0 (inferInstance : MeasurableSpace SampleSpace) :=
  AmbientNullAugmentation.filtration gaussianProduct (naturalPast κ)

def prefixPath (κ T : ℝ≥0) (ω : SampleSpace) : C(Iic T, ℝ) :=
  (changedPath κ ω).comp ⟨Subtype.val,continuous_subtype_val⟩

theorem prefix_measurable (κ T : ℝ≥0) : Measurable[naturalPast κ T] (prefixPath κ T) := by
  letI : MeasurableSpace SampleSpace := naturalPast κ T
  letI : LocallyCompactSpace (Iic T) := isClosed_Iic.locallyCompactSpace
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  exact ((state_stronglyAdapted κ r).mono ((naturalPast κ).mono r.property)).measurable

def extend (T : ℝ≥0) (p : C(Iic T, ℝ)) : C(ℝ≥0, ℝ) :=
  p.comp ⟨fun s => ⟨min s T,min_le_right s T⟩,
    (continuous_id.min continuous_const).subtype_mk _⟩

theorem extend_measurable (T : ℝ≥0) : Measurable (extend T) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro s
  exact ContinuousMap.measurable_eval (⟨min s T,min_le_right s T⟩ : Iic T)

theorem extend_prefix_upto (κ T : ℝ≥0) (ω : SampleSpace) (s : ℝ≥0) (hs : s ≤ T) :
    extend T (prefixPath κ T ω) s = changedPath κ ω s := by
  change changedPath κ ω (min s T) = _
  rw [min_eq_left hs]

theorem inverse_observed_past (κ T : ℝ≥0) :
    Measurable[augmentedNaturalPast κ T] (fun ω => inverse κ ω T) := by
  have hr : Measurable[naturalPast κ T]
      (fun ω => inverseFromPath (extend T (prefixPath κ T ω)) T) :=
    inverseFromPath_joint.comp
      (((extend_measurable T).comp (prefix_measurable κ T)).prodMk measurable_const)
  have he : (fun ω => inverseFromPath (extend T (prefixPath κ T ω)) T) =ᵐ[gaussianProduct]
      (fun ω => inverse κ ω T) := by
    filter_upwards [inverse_recovery] with ω hω
    rw [inverseFromPath_congr_upto _ (changedPath κ ω) T (extend_prefix_upto κ T ω)]
    exact hω κ T
  exact AmbientNullAugmentation.measurable_of_raw_aestronglyMeasurable
    (naturalPast κ T) gaussianProduct (inverse_coordinate_measurable κ T)
    (hr.stronglyMeasurable.aestronglyMeasurable.congr he)

theorem inverse_stronglyAdapted (κ : ℝ≥0) :
    StronglyAdapted (augmentedNaturalPast κ) (fun t ω => inverse κ ω t) :=
  fun t => (inverse_observed_past κ t).stronglyMeasurable

end OperatorDerivativeRewrite.Foundation.StickyNaturalClock
