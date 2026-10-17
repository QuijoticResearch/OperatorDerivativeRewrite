import Foundation.HigherHeatFourierTests
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Actual absolutely convergent Fourier cylinder series with uniformly controlled higher-heat expectations. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierSeries
open SignedDensityIntegral HigherHeatCylinderFourier HigherHeatDyadicLaws HigherHeatFourierTests

variable (n : ℕ) (a : ℕ → ℂ) (ξ : ℕ → Grid n)

def series (y : Grid n) : ℂ := ∑' k, a k*configurationPhase (ξ k) y

theorem term_norm (k : ℕ) (y : Grid n) : ‖a k*configurationPhase (ξ k) y‖=‖a k‖ := by
  rw [norm_mul,configurationPhase_norm,mul_one]

theorem series_summable (ha : Summable (fun k => ‖a k‖)) (y : Grid n) :
    Summable (fun k => a k*configurationPhase (ξ k) y) :=
  ha.of_norm_bounded (fun k => (term_norm n a ξ k y).le)

theorem series_continuous (ha : Summable (fun k => ‖a k‖)) : Continuous (series n a ξ) := by
  exact continuous_tsum (fun k => by unfold configurationPhase; fun_prop) ha
    (fun k y => (term_norm n a ξ k y).le)

theorem series_bound (ha : Summable (fun k => ‖a k‖)) (y : Grid n) :
    ‖series n a ξ y‖ ≤ ∑' k, ‖a k‖ := by
  have ht : Summable (fun k => ‖a k*configurationPhase (ξ k) y‖) := by
    simpa only [term_norm] using ha
  simpa only [series,term_norm] using norm_tsum_le_tsum_norm ht

def test (ha : Summable (fun k => ‖a k‖)) : Grid n →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (series n a ξ) (series_continuous n a ξ ha)
    (∑' k, ‖a k‖) (series_bound n a ξ ha)

theorem series_expectation (ha : Summable (fun k => ‖a k‖))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    (∫ᵛ y : Grid n, series n a ξ y ∂<•HigherHeatDyadicLaws.law m hm T hT n)=
      ∑' k, a k * ∏ j : Fin (gridSize n), HigherHeatL2.symbol m (duration T n)
        (∑ i ∈ Finset.univ.filter (fun i => j ≤ i), ξ k i) := by
  let ν := HigherHeatDyadicLaws.law m hm T hT n
  letI : IsFiniteMeasure ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  have hs := VectorMeasure.hasSum_integral_of_dominated_convergence
    (μ := ν) (B := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip)
    (f := series n a ξ)
    (fun k _ => ‖a k‖)
    (fun k => ((measurable_const.mul (configurationPhase_measurable (ξ k))) :
      Measurable (fun y : Grid n => a k*configurationPhase (ξ k) y)).aestronglyMeasurable)
    (fun k => Eventually.of_forall fun y => (term_norm n a ξ k y).le)
    (Eventually.of_forall fun _ => ha) (integrable_const _)
    (Eventually.of_forall fun y => (series_summable n a ξ ha y).hasSum)
  change (∫ᵛ y : Grid n, series n a ξ y ∂<•ν)=_
  rw [← hs.tsum_eq]
  apply tsum_congr
  intro k
  change (∫ᵛ y : Grid n, a k*configurationPhase (ξ k) y ∂<•ν)=_
  rw [signed_integral_complex_mul _ _ (configurationPhase_measurable _) 1
    (fun y => by rw [configurationPhase_norm])]
  dsimp only [ν]
  rw [HigherHeatDyadicLaws.law,positionLaw_fourier]

theorem series_spectral_bound (ha : Summable (fun k => ‖a k‖))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ‖∫ᵛ y : Grid n, series n a ξ y ∂<•HigherHeatDyadicLaws.law m hm T hT n‖ ≤
      ∑' k, ‖a k‖ := by
  rw [series_expectation n a ξ ha]
  have hb k : ‖a k * ∏ j : Fin (gridSize n), HigherHeatL2.symbol m (duration T n)
      (∑ i ∈ Finset.univ.filter (fun i => j ≤ i), ξ k i)‖ ≤ ‖a k‖ := by
    rw [norm_mul,norm_prod]
    apply mul_le_of_le_one_right (norm_nonneg _)
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => HigherHeatL2.symbol_norm_le _ _ _)
  have hn := Summable.of_nonneg_of_le (fun k => norm_nonneg _) hb ha
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hb ha)

theorem actual_path_series (ha : Summable (fun k => ‖a k‖)) :
    Continuous (fun ω : HigherHeatContinuousCylinders.Path =>
      series n a ξ (HigherHeatContinuousCylinders.sample n ω)) ∧
    ∀ ω : HigherHeatContinuousCylinders.Path,
      ‖series n a ξ (HigherHeatContinuousCylinders.sample n ω)‖ ≤ ∑' k, ‖a k‖ :=
  ⟨(series_continuous n a ξ ha).comp (HigherHeatContinuousCylinders.sample_continuous n),
    fun _ => series_bound n a ξ ha _⟩

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierSeries
