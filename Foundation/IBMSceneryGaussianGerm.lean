import Foundation.GaussianVanishingPrediction
import Foundation.IBMFoldedSourceCovariance
import Foundation.SPDEWickBrownianPrediction

/-! Shrinking positive-scenery Gaussian histories lose every finite-ridge
nonlinear prediction. Histories are the actual Gaussian coordinate classes.
Identifying their completed sigma algebra with the path-based IBM localization
histories, and then controlling the clock germ, remain separate obligations. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSceneryGaussianGerm
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection
open GaussianVanishingPrediction GaussianSingleObservationPrediction

def direction (r : ℝ≥0) : CoefficientSpace := IBMFoldedSourceCovariance.direction r
def history (δ r : ℝ≥0) : CoefficientSpace := direction (min r δ)

theorem history_actual (δ r : ℝ≥0) :
    firstChaosEmbedding (history δ r) =ᵐ[gaussianProduct]
      fun X => IBMConstructedSources.sceneryPath X (min r δ : ℝ≥0) := by
  change firstChaosEmbedding (IBMActualQuarticMoment.sceneryDirection
    |((min r δ : ℝ≥0) : ℝ)|) =ᵐ[gaussianProduct] _
  rw [abs_of_nonneg (min r δ).coe_nonneg]
  exact (IBMActualQuarticMoment.scenery_firstChaos_ae _).symm

theorem direction_inner (r s : ℝ≥0) :
    inner ℝ (direction r) (direction s) = min (r : ℝ) s := by
  simpa only [direction, abs_of_nonneg r.coe_nonneg, abs_of_nonneg s.coe_nonneg] using
    IBMFoldedSourceCovariance.gram r s

theorem source_prediction (δ r : ℝ≥0) :
    sourceProjection (history δ) (direction r) = direction (min r δ) := by
  apply SPDEWickBrownianPrediction.sourceProjection_eq_of_pairings
  · exact (Submodule.span ℝ (range (history δ))).le_topologicalClosure
      (Submodule.subset_span ⟨r,rfl⟩)
  · intro s
    rw [history, direction_inner, direction_inner]
    simp only [NNReal.coe_min]
    rw [min_assoc, min_eq_right (min_le_right (s : ℝ) δ)]

theorem source_prediction_tendsto (r : ℝ≥0) (δ : ℕ → ℝ≥0)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => sourceProjection (history (δ n)) (direction r)) atTop (𝓝 0) := by
  have hdir : Continuous direction := by
    change Continuous (fun r : ℝ≥0 => IBMSineSourceField.direction |(r : ℝ)|)
    exact IBMSineSourceField.direction_continuous.comp (continuous_abs.comp NNReal.continuous_coe)
  have hz : direction 0 = 0 := by
    have hi := direction_inner 0 0
    rw [real_inner_self_eq_norm_sq] at hi
    norm_num at hi
    exact hi
  have ht : Tendsto (fun n => min r (δ n)) atTop (𝓝 0) := by
    simpa only [min_zero] using (tendsto_const_nhds (x := r)).min hδ
  simpa only [source_prediction, hz, Function.comp_def] using (hdir.tendsto 0).comp ht

theorem finite_ridge_prediction_tendsto {J : Type*} [Fintype J]
    (b : J → ℝ) (r : J → ℝ≥0) (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => sourceProjection (history (δ n)) (∑ j, b j • direction (r j)))
      atTop (𝓝 0) := by
  have ht := tendsto_finsetSum Finset.univ (fun j _ =>
    (source_prediction_tendsto (r j) δ hδ).const_smul (b j))
  simpa only [map_sum, map_smul, smul_zero, Finset.sum_const_zero] using ht

theorem nonlinear_finite_ridge_tendsto {J : Type*} [Fintype J]
    (b : J → ℝ) (r : J → ℝ≥0) (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (F : GaussianL2) (hF : F ∈ singleGenerated (∑ j, b j • direction (r j))) :
    Tendsto (fun n => conditionalProjection (history (δ n)) F) atTop
      (𝓝 ((∫ ω, F ω ∂gaussianProduct) • gaussianOne)) := by
  simpa only [meanProjection_apply] using single_tendsto (fun n => history (δ n))
    _ (finite_ridge_prediction_tendsto b r δ hδ) F hF

theorem persistent_finite_ridge_constant {J : Type*} [Fintype J]
    (b : J → ℝ) (r : J → ℝ≥0) (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (F : GaussianL2) (hF : F ∈ singleGenerated (∑ j, b j • direction (r j)))
    (hp : ∀ n, F ∈ generated (history (δ n))) :
    F = (∫ ω, F ω ∂gaussianProduct) • gaussianOne :=
  persistent_single_constant (fun n => history (δ n))
    _ (finite_ridge_prediction_tendsto b r δ hδ) F hF hp

end OperatorDerivativeRewrite.Foundation.IBMSceneryGaussianGerm
