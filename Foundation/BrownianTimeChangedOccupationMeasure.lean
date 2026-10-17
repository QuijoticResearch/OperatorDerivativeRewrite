import Foundation.BrownianClockMeasureTransport
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! The complete spatial occupation measure of the actual time-changed path.
The singular clock contribution becomes an explicit atom at zero. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianTimeChangedOccupationMeasure
open InfiniteGaussian IBMConstructedSources BrownianMassStieltjesSupport
open BrownianRandomMassClock BrownianMassRandomTimeChange BrownianClockMeasureTransport
set_option backward.isDefEq.respectTransparency false

def originalOccupation (ω : SampleSpace) (T : ℝ≥0) : Measure ℝ :=
  Measure.map (clockPath ω) (ordinaryTime.restrict (Iic T))

def changedOccupation (κ : ℝ≥0) (ω : SampleSpace) (T : ℝ≥0) : Measure ℝ :=
  Measure.map (changedPath κ ω) (ordinaryTime.restrict (Iic T))

theorem restricted_transport (κ : ℝ≥0) (ω : SampleSpace) (T : ℝ≥0) :
    ordinaryTime.restrict (Iic T) = Measure.map (forward κ ω)
      ((clockMeasure κ ω).restrict (Iic (inverse κ ω T))) := by
  rw [← forward_preimage_Iic κ ω T,
    ← Measure.restrict_map (forward_continuous κ ω).measurable measurableSet_Iic,
    forward_map_clockMeasure]

theorem changedOccupation_total (κ : ℝ≥0) (ω : SampleSpace) (T : ℝ≥0) :
    changedOccupation κ ω T univ = (T : ℝ≥0∞) := by
  rw [changedOccupation, Measure.map_apply (changedPath κ ω).continuous.measurable MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply_univ, ordinaryTime_Iic]

theorem originalOccupation_total (ω : SampleSpace) (T : ℝ≥0) :
    originalOccupation ω T univ = (T : ℝ≥0∞) := by
  rw [originalOccupation, Measure.map_apply (clockPath ω).continuous.measurable MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply_univ, ordinaryTime_Iic]

theorem occupation_decomposition : ∀ᵐ ω ∂gaussianProduct, ∀ κ T : ℝ≥0,
    changedOccupation κ ω T = originalOccupation ω (inverse κ ω T)+
      ((κ : ℝ≥0∞)*(mass ω (inverse κ ω T) : ℝ≥0∞)) • Measure.dirac (0 : ℝ) := by
  filter_upwards [concentrated_on_zeros] with ω hω κ T
  have hz : (clockPath ω : ℝ≥0 → ℝ) =ᵐ[(massMeasure ω).restrict (Iic (inverse κ ω T))]
      fun _ => 0 := ae_restrict_of_ae (ae_iff.mpr hω)
  have he : (changedPath κ ω : ℝ≥0 → ℝ) ∘ forward κ ω = clockPath ω := by
    funext s
    exact recover_original κ ω s
  rw [changedOccupation, restricted_transport, Measure.map_map
    (changedPath κ ω).continuous.measurable (forward_continuous κ ω).measurable, he,
    clockMeasure, Measure.restrict_add, Measure.restrict_smul,
    Measure.map_add _ _ (clockPath ω).continuous.measurable, Measure.map_smul,
    Measure.map_congr hz, Measure.map_const, Measure.restrict_apply_univ, massMeasure_Iic]
  rw [smul_smul]
  · rfl
  · exact (clockPath ω).continuous.measurable.aemeasurable

end OperatorDerivativeRewrite.Foundation.BrownianTimeChangedOccupationMeasure
