import Foundation.BrownianMassMeasurableKernel
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! A time-local-time measure pushed through the same Brownian observation
collapses to an atom at zero. This is distinct from a spatial reference law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianMassObservationCollapse
open InfiniteGaussian IBMConstructedSources BrownianMassContinuousLimit
open BrownianMassStieltjesSupport BrownianMassMeasurableKernel

def observedMass (T : ℝ≥0) (ω : SampleSpace) : Measure ℝ :=
  Measure.map (clockPath ω) (restrictedMass T ω)

theorem observedMass_eq : ∀ᵐ ω ∂gaussianProduct, ∀ T : ℝ≥0,
    observedMass T ω = ENNReal.ofReal (limitPath ω T) • Measure.dirac (0 : ℝ) := by
  filter_upwards [concentrated_on_zeros, limitPath_properties] with ω hc hp T
  have hz : (clockPath ω : ℝ≥0 → ℝ) =ᵐ[restrictedMass T ω] fun _ => 0 := by
    have h : ∀ᵐ t ∂massMeasure ω, clockPath ω t = 0 := ae_iff.mpr hc
    exact ae_restrict_of_ae h
  rw [observedMass, Measure.map_congr hz, Measure.map_const,
    restrictedMass, Measure.restrict_apply_univ, massMeasure_Icc,
    cumulative_eq hp.2.1, cumulative_eq hp.2.1, hp.1, sub_zero]

theorem observedMass_away_zero : ∀ᵐ ω ∂gaussianProduct, ∀ T : ℝ≥0,
    observedMass T ω (Ioc (1 : ℝ) 2) = 0 := by
  filter_upwards [observedMass_eq] with ω hω T
  rw [hω T]
  simp [Measure.smul_apply]

theorem observedMass_ne_volume : ∀ᵐ ω ∂gaussianProduct, ∀ T : ℝ≥0,
    observedMass T ω ≠ (volume : Measure ℝ) := by
  filter_upwards [observedMass_away_zero] with ω hω T he
  have h := hω T
  rw [he, Real.volume_Ioc] at h
  norm_num at h

end OperatorDerivativeRewrite.Foundation.BrownianMassObservationCollapse
