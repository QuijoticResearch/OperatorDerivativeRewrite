import Foundation.HigherHeatInterpolatedFourier
import Mathlib.Analysis.Normed.Group.Tannery

/-! Actual mixed-level infinite path observables with convergent higher-heat weighted expectations. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatMixedFourierPaths
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatInterpolatedPaths
open HigherHeatWeightedPaths HigherHeatCylinderPathLimit HigherHeatInterpolatedFourier
open SignedDensityIntegral HigherHeatFourierTests

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def character (i : ℕ) (ω : Path) : ℂ := configurationPhase (ξ i) (sample (levels i) ω)

theorem character_continuous (i : ℕ) : Continuous (character levels ξ i) := by
  have hc : Continuous (configurationPhase (ξ i)) := by unfold configurationPhase; fun_prop
  exact hc.comp (sample_continuous (levels i))

theorem character_norm (i : ℕ) (ω : Path) : ‖character levels ξ i ω‖=1 :=
  configurationPhase_norm _ _

def expectedCharacter (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (i : ℕ) : ℂ :=
  ∫ᵛ y, configurationPhase (ξ i) y ∂<•law m hm T hT (levels i)

theorem character_expectation_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n i : ℕ) :
    ‖∫ᵛ ω, character levels ξ i ω ∂<•signedPath m hm T hT n‖ ≤ 1 :=
  phase_expectation_bound m hm T hT n (sampleTime (levels i)) (ξ i)

theorem character_expectation_coarse (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n i : ℕ) (hin : levels i ≤ n) :
    (∫ᵛ ω, character levels ξ i ω ∂<•signedPath m hm T hT n)=expectedCharacter levels ξ m hm T hT i := by
  let f : Grid (levels i) →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (configurationPhase (ξ i)) (by unfold configurationPhase; fun_prop)
    1 (fun y => (configurationPhase_norm (ξ i) y).le)
  exact complex_integral_coarse m hm T hT (levels i) n hin f

theorem character_expectation_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    Tendsto (fun n => ∫ᵛ ω, character levels ξ i ω ∂<•signedPath m hm T hT n) atTop
      (𝓝 (expectedCharacter levels ξ m hm T hT i)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (levels i)] with n hn
  exact (character_expectation_coarse levels ξ m hm T hT n i hn).symm

variable (a : ℕ → ℂ)

def series (ω : Path) : ℂ := ∑' i, a i * character levels ξ i ω

theorem term_norm (i : ℕ) (ω : Path) : ‖a i * character levels ξ i ω‖=‖a i‖ := by
  rw [norm_mul, character_norm, mul_one]

theorem series_summable (ha : Summable (fun i => ‖a i‖)) (ω : Path) :
    Summable (fun i => a i * character levels ξ i ω) :=
  ha.of_norm_bounded (fun i => (term_norm levels ξ a i ω).le)

theorem series_continuous (ha : Summable (fun i => ‖a i‖)) : Continuous (series levels ξ a) :=
  continuous_tsum (fun i => continuous_const.mul (character_continuous levels ξ i)) ha
    (fun i ω => (term_norm levels ξ a i ω).le)

theorem series_bound (ha : Summable (fun i => ‖a i‖)) (ω : Path) :
    ‖series levels ξ a ω‖ ≤ ∑' i, ‖a i‖ := by
  have hs : Summable (fun i => ‖a i * character levels ξ i ω‖) := by
    simpa only [term_norm] using ha
  simpa only [series, term_norm] using norm_tsum_le_tsum_norm hs

def test (ha : Summable (fun i => ‖a i‖)) : Path →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (series levels ξ a) (series_continuous levels ξ a ha)
    (∑' i, ‖a i‖) (series_bound levels ξ a ha)

theorem series_integrable (ha : Summable (fun i => ‖a i‖))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (signedPath m hm T hT n).Integrable (series levels ξ a) :=
  bounded_signed_integrable _ _ (series_continuous levels ξ a ha).measurable _
    (series_bound levels ξ a ha)

theorem series_expectation (ha : Summable (fun i => ‖a i‖))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫ᵛ ω, series levels ξ a ω ∂<•signedPath m hm T hT n)=
      ∑' i, a i * ∫ᵛ ω, character levels ξ i ω ∂<•signedPath m hm T hT n := by
  let ν := signedPath m hm T hT n
  letI : IsFiniteMeasure ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  have hs := VectorMeasure.hasSum_integral_of_dominated_convergence
    (μ := ν) (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip)
    (f := series levels ξ a) (fun i _ => ‖a i‖)
    (fun i => (measurable_const.mul (character_continuous levels ξ i).measurable).aestronglyMeasurable)
    (fun i => Eventually.of_forall fun ω => (term_norm levels ξ a i ω).le)
    (Eventually.of_forall fun _ => ha) (integrable_const _)
    (Eventually.of_forall fun ω => (series_summable levels ξ a ha ω).hasSum)
  rw [← hs.tsum_eq]
  apply tsum_congr
  intro i
  exact signed_integral_complex_mul ν _ (character_continuous levels ξ i).measurable 1
    (fun ω => (character_norm levels ξ i ω).le) (a i)

theorem term_expectation_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n i : ℕ) :
    ‖a i * ∫ᵛ ω, character levels ξ i ω ∂<•signedPath m hm T hT n‖ ≤ ‖a i‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (character_expectation_bound levels ξ m hm T hT n i)

theorem series_expectation_bound (ha : Summable (fun i => ‖a i‖))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ‖∫ᵛ ω, series levels ξ a ω ∂<•signedPath m hm T hT n‖ ≤ ∑' i, ‖a i‖ := by
  rw [series_expectation levels ξ a ha]
  have hb := term_expectation_bound levels ξ a m hm T hT n
  have hs := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hb ha
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb ha)

def expectedSeries (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : ℂ :=
  ∑' i, a i * expectedCharacter levels ξ m hm T hT i

theorem series_expectation_tendsto (ha : Summable (fun i => ‖a i‖))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ∫ᵛ ω, series levels ξ a ω ∂<•signedPath m hm T hT n) atTop
      (𝓝 (expectedSeries levels ξ a m hm T hT)) := by
  have ht := tendsto_tsum_of_dominated_convergence ha
    (fun i => tendsto_const_nhds.mul (character_expectation_tendsto levels ξ m hm T hT i))
    (Eventually.of_forall (term_expectation_bound levels ξ a m hm T hT))
  apply ht.congr'
  exact Eventually.of_forall fun n => (series_expectation levels ξ a ha m hm T hT n).symm

theorem expectedSeries_bound (ha : Summable (fun i => ‖a i‖))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ‖expectedSeries levels ξ a m hm T hT‖ ≤ ∑' i, ‖a i‖ :=
  le_of_tendsto (series_expectation_tendsto levels ξ a ha m hm T hT).norm
    (Eventually.of_forall (series_expectation_bound levels ξ a ha m hm T hT))

theorem weighted_series_integrable (ha : Summable (fun i => ‖a i‖))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    Integrable (fun ω => pathWeight m hm T hT n ω • series levels ξ a ω) (probabilityPath m hm T hT n) :=
  path_weighted_integrable m hm T hT n _ (series_integrable levels ξ a ha m hm T hT n)

theorem weighted_series_tendsto (ha : Summable (fun i => ‖a i‖))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ∫ ω, pathWeight m hm T hT n ω • series levels ξ a ω ∂probabilityPath m hm T hT n)
      atTop (𝓝 (expectedSeries levels ξ a m hm T hT)) := by
  apply (series_expectation_tendsto levels ξ a ha m hm T hT).congr'
  exact Eventually.of_forall fun n => signedPath_expectation m hm T hT n _
    (series_integrable levels ξ a ha m hm T hT n)

theorem representation_independent (ha : Summable (fun i => ‖a i‖))
    (otherLevels : ℕ → ℕ) (otherξ : (i : ℕ) → Grid (otherLevels i)) (b : ℕ → ℂ)
    (hb : Summable (fun i => ‖b i‖))
    (he : ∀ ω, series levels ξ a ω=series otherLevels otherξ b ω)
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    expectedSeries levels ξ a m hm T hT=expectedSeries otherLevels otherξ b m hm T hT := by
  have hi : ∀ n, (∫ᵛ ω, series levels ξ a ω ∂<•signedPath m hm T hT n)=
      ∫ᵛ ω, series otherLevels otherξ b ω ∂<•signedPath m hm T hT n := by
    intro n
    apply VectorMeasure.integral_congr_ae
    exact Eventually.of_forall he
  exact tendsto_nhds_unique
    ((series_expectation_tendsto levels ξ a ha m hm T hT).congr' (Eventually.of_forall hi))
    (series_expectation_tendsto otherLevels otherξ b hb m hm T hT)

end OperatorDerivativeRewrite.Foundation.HigherHeatMixedFourierPaths
