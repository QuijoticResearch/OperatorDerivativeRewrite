import Foundation.GeneratedFamilyModification
import Foundation.IBMSceneryGaussianGerm
import Foundation.IBMSpatialSceneryForecast

/-! Equality of the completed Gaussian scenery history L2 space with the
ACTUAL path-based spatial history used by IBM localization. No simultaneous
uncountable-coordinate AE equality is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSceneryHistoryBridge
open InfiniteGaussian GaussianConditionalGraph IBMSceneryGaussianGerm

def actualFamily (δ : ℝ≥0) (X : SampleSpace) (r : ℝ≥0) : ℝ :=
  IBMConstructedSources.sceneryPath X (min r δ : ℝ≥0)

def actualPast (δ : ℝ≥0) (X : SampleSpace) (r : Iic δ) : ℝ :=
  IBMSpatialSceneryForecast.scenery r.val X

theorem path_history_eq_comap (δ : ℝ≥0) :
    IBMSpatialSceneryForecast.history δ = MeasurableSpace.comap (actualPast δ) inferInstance := by
  rw [IBMSpatialSceneryForecast.history, Filtration.natural_eq_comap]
  rfl

theorem family_lpMeas_eq (δ : ℝ≥0) :
    lpMeas ℝ ℝ (MeasurableSpace.comap (actualFamily δ) inferInstance) 2 gaussianProduct =
      lpMeas ℝ ℝ (IBMSpatialSceneryForecast.history δ) 2 gaussianProduct := by
  rw [path_history_eq_comap]
  apply le_antisymm
  · intro F hF
    let k : (Iic δ → ℝ) → ℝ≥0 → ℝ := fun p r => p ⟨min r δ, mem_Iic.mpr (min_le_right _ _)⟩
    have hk : Measurable k := Measurable.of_eval fun r => measurable_pi_apply _
    have he : actualFamily δ =ᵐ[gaussianProduct] k ∘ actualPast δ :=
      EventuallyEq.of_eq rfl
    exact aestronglyMeasurable_comap_of_ae_factor hk he hF
  · intro F hF
    let k : (ℝ≥0 → ℝ) → Iic δ → ℝ := fun p r => p r.val
    have hk : Measurable k := Measurable.of_eval fun r => measurable_pi_apply _
    have he : actualPast δ =ᵐ[gaussianProduct] k ∘ actualFamily δ := by
      apply EventuallyEq.of_eq
      funext X r
      simp only [actualPast, actualFamily, Function.comp_apply, k,
        min_eq_left (mem_Iic.mp r.property), IBMSpatialSceneryForecast.scenery]
    exact aestronglyMeasurable_comap_of_ae_factor hk he hF

theorem generated_eq_path_history (δ : ℝ≥0) :
    generated (IBMSceneryGaussianGerm.history δ) =
      lpMeas ℝ ℝ (IBMSpatialSceneryForecast.history δ) 2 gaussianProduct := by
  rw [generated, GeneratedFamilyModification.lpMeas_eq gaussianProduct
    (firstChaosFamily (IBMSceneryGaussianGerm.history δ)) (actualFamily δ)
    (fun r => IBMSceneryGaussianGerm.history_actual δ r), family_lpMeas_eq]

theorem projection_eq_condExpL2 (δ : ℝ≥0) (F : GaussianL2) :
    conditionalProjection (IBMSceneryGaussianGerm.history δ) F =
      (condExpL2 ℝ ℝ (IBMSpatialSceneryForecast.history.le δ) F : GaussianL2) := by
  change (generated (IBMSceneryGaussianGerm.history δ)).starProjection F = _
  apply (generated (IBMSceneryGaussianGerm.history δ)).eq_starProjection_of_mem_of_inner_eq_zero
  · rw [generated_eq_path_history]
    exact (condExpL2 ℝ ℝ (IBMSpatialSceneryForecast.history.le δ) F).property
  · intro G hG
    rw [generated_eq_path_history] at hG
    rw [inner_sub_left, inner_condExpL2_eq_inner_fun (𝕜 := ℝ)
      (IBMSpatialSceneryForecast.history.le δ) F G hG, sub_self]

theorem mem_generated_iff_path (δ : ℝ≥0) (F : GaussianL2) :
    F ∈ generated (IBMSceneryGaussianGerm.history δ) ↔
      AEStronglyMeasurable[IBMSpatialSceneryForecast.history δ] F gaussianProduct := by
  rw [generated_eq_path_history]
  rfl

theorem projection_ae_path_condExp (δ : ℝ≥0) (F : GaussianL2) :
    conditionalProjection (IBMSceneryGaussianGerm.history δ) F =ᵐ[gaussianProduct]
      gaussianProduct[F | IBMSpatialSceneryForecast.history δ] := by
  rw [projection_eq_condExpL2]
  simpa only [Lp.toLp_coeFn] using (Lp.memLp F).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) (IBMSpatialSceneryForecast.history.le δ)

theorem nonlinear_path_prediction_tendsto {J : Type*} [Fintype J]
    (b : J → ℝ) (r : J → ℝ≥0) (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (F : GaussianL2) (hF : F ∈ GaussianSingleObservationPrediction.singleGenerated
      (∑ j, b j • direction (r j))) :
    Tendsto (fun n => (condExpL2 ℝ ℝ (IBMSpatialSceneryForecast.history.le (δ n)) F : GaussianL2))
      atTop (𝓝 ((∫ ω, F ω ∂gaussianProduct) • gaussianOne)) := by
  simpa only [projection_eq_condExpL2] using nonlinear_finite_ridge_tendsto b r δ hδ F hF

theorem persistent_path_ridge_constant {J : Type*} [Fintype J]
    (b : J → ℝ) (r : J → ℝ≥0) (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (F : GaussianL2) (hF : F ∈ GaussianSingleObservationPrediction.singleGenerated
      (∑ j, b j • direction (r j)))
    (hp : ∀ n, AEStronglyMeasurable[IBMSpatialSceneryForecast.history (δ n)] F gaussianProduct) :
    F = (∫ ω, F ω ∂gaussianProduct) • gaussianOne :=
  persistent_finite_ridge_constant b r δ hδ F hF
    (fun n => (mem_generated_iff_path (δ n) F).mpr (hp n))

end OperatorDerivativeRewrite.Foundation.IBMSceneryHistoryBridge
