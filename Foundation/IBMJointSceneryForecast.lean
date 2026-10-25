import Foundation.IBMSceneryHistoryBridge
import Foundation.IBMFiniteRidgeObservation
import Foundation.BochnerL2Approximation

/-! Conditional scenery forecasts lifted through the actual IBM source unitary.
The limit below concerns source conditioning, not the full observed IBM germ. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMJointSceneryForecast
open InfiniteGaussian IBMIntrinsicOperators IBMTimeAveragedObservable
open GaussianConditionalGraph GaussianVanishingPrediction
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def spatial (δ : ℝ≥0) : GaussianL2 →L[ℝ] GaussianL2 :=
  conditionalProjection (IBMSceneryGaussianGerm.history δ)

def field (δ : ℝ≥0) : ScalarFieldSpace →L[ℝ] ScalarFieldSpace :=
  (spatial δ).compLpL 2 gaussianProduct

def forecast (δ : ℝ≥0) (F : JointL2) : JointL2 :=
  sourceUnitary.symm (field δ (sourceUnitary F))

def vacuumField : ScalarFieldSpace →L[ℝ] ScalarFieldSpace :=
  meanProjection.compLpL 2 gaussianProduct

def sourceMean (F : JointL2) : JointL2 :=
  sourceUnitary.symm (vacuumField (sourceUnitary F))

theorem field_sections (δ : ℝ≥0) (f : ScalarFieldSpace) :
    field δ f =ᵐ[gaussianProduct] fun Y =>
      (condExpL2 ℝ ℝ (IBMSpatialSceneryForecast.history.le δ) (f Y) : GaussianL2) := by
  filter_upwards [(spatial δ).coeFn_compLpL f] with Y hY
  exact hY.trans (IBMSceneryHistoryBridge.projection_eq_condExpL2 δ (f Y))

theorem field_norm_le (δ : ℝ≥0) (f : ScalarFieldSpace) : ‖field δ f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(spatial δ).coeFn_compLpL f] with Y hY
  change ‖((spatial δ).compLpL 2 gaussianProduct f) Y‖ ≤ _
  rw [hY]
  exact conditionalProjection_norm_le _ _

theorem forecast_norm_le (δ : ℝ≥0) (F : JointL2) : ‖forecast δ F‖ ≤ ‖F‖ := by
  simpa only [forecast, LinearIsometryEquiv.norm_map] using field_norm_le δ (sourceUnitary F)

theorem vacuum_sections (f : ScalarFieldSpace) :
    vacuumField f =ᵐ[gaussianProduct] fun Y => meanProjection (f Y) :=
  meanProjection.coeFn_compLpL f

theorem field_tendsto (δ : ℕ → ℝ≥0) (f : ScalarFieldSpace)
    (ht : ∀ᵐ Y ∂gaussianProduct, Tendsto (fun n => spatial (δ n) (f Y)) atTop
      (𝓝 (meanProjection (f Y)))) :
    Tendsto (fun n => field (δ n) f) atTop (𝓝 (vacuumField f)) := by
  let b : GaussianL2 := (Lp.memLp f).norm.toLp (fun Y => ‖f Y‖)
  have hb : b =ᵐ[gaussianProduct] fun Y => ‖f Y‖ := MemLp.coeFn_toLp _
  apply BochnerL2Approximation.tendsto_of_dominated _ _ b
  · intro n
    filter_upwards [(spatial (δ n)).coeFn_compLpL f, hb] with Y hY hbY
    change ‖((spatial (δ n)).compLpL 2 gaussianProduct f) Y‖ ≤ _
    rw [hY,hbY,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact conditionalProjection_norm_le _ _
  · filter_upwards [vacuum_sections f, ht, hb] with Y hY htY hbY
    rw [hY,hbY,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact le_of_tendsto htY.norm (Eventually.of_forall fun n =>
      conditionalProjection_norm_le _ _)
  · filter_upwards [ae_all_iff.mpr (fun n => (spatial (δ n)).coeFn_compLpL f),
      vacuum_sections f, ht] with Y hY hv htY
    change Tendsto (fun n => ((spatial (δ n)).compLpL 2 gaussianProduct f) Y) _ _
    simpa only [hY,hv] using htY

theorem forecast_tendsto (δ : ℕ → ℝ≥0) (F : JointL2)
    (ht : ∀ᵐ Y ∂gaussianProduct, Tendsto (fun n => spatial (δ n) (sourceUnitary F Y))
      atTop (𝓝 (meanProjection (sourceUnitary F Y)))) :
    Tendsto (fun n => forecast (δ n) F) atTop (𝓝 (sourceMean F)) :=
  sourceUnitary.symm.continuous.tendsto _ |>.comp (field_tendsto δ (sourceUnitary F) ht)

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (r : ι → ℝ≥0)

theorem ridge_direction (Y : SampleSpace) : IBMFiniteRidgeObservation.direction a r Y =
    ∑ i, a i • IBMSceneryGaussianGerm.direction
      ⟨|GaussianTimeProcess.process (r i) Y|,abs_nonneg _⟩ := by
  unfold IBMFiniteRidgeObservation.direction
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  change IBMActualQuarticMoment.sceneryDirection |GaussianTimeProcess.process (r i) Y| =
    IBMActualQuarticMoment.sceneryDirection |(⟨|GaussianTimeProcess.process (r i) Y|,
      abs_nonneg _⟩ : ℝ≥0)|
  simp

theorem ridge_forecast_tendsto {φ : ℝ → ℝ} (hc : Continuous φ) {A : ℝ}
    (hA : ∀ x, ‖φ x‖ ≤ A) (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => forecast (δ n) (IBMFiniteRidgeObservation.jointClass a r hc hA))
      atTop (𝓝 (sourceMean (IBMFiniteRidgeObservation.jointClass a r hc hA))) := by
  apply forecast_tendsto
  filter_upwards [IBMFiniteRidgeObservation.source_sections a r hc hA] with Y hY
  rw [hY]
  have hh := IBMFirstChaosMixedStein.testClass_generated
    (IBMFiniteRidgeObservation.direction a r Y) hc hA
  have hm : IBMFirstChaosMixedStein.testClass
      (IBMFiniteRidgeObservation.direction a r Y) hc hA ∈
      GaussianSingleObservationPrediction.singleGenerated
        (∑ i, a i • IBMSceneryGaussianGerm.direction
        ⟨|GaussianTimeProcess.process (r i) Y|,abs_nonneg _⟩) := by
    simpa only [GaussianSingleObservationPrediction.singleGenerated,
      ← ridge_direction a r Y] using hh
  simpa only [spatial, meanProjection_apply] using
    IBMSceneryGaussianGerm.nonlinear_finite_ridge_tendsto a
      (fun i => ⟨|GaussianTimeProcess.process (r i) Y|,abs_nonneg _⟩) δ hδ
      (IBMFirstChaosMixedStein.testClass (IBMFiniteRidgeObservation.direction a r Y) hc hA) hm


theorem field_fixed_iff (δ : ℝ≥0) (f : ScalarFieldSpace) : field δ f = f ↔
    ∀ᵐ Y ∂gaussianProduct,
      AEStronglyMeasurable[IBMSpatialSceneryForecast.history δ] (f Y) gaussianProduct := by
  constructor
  · intro he
    filter_upwards [(spatial δ).coeFn_compLpL f] with Y hY
    change field δ f Y = spatial δ (f Y) at hY
    rw [he] at hY
    apply (IBMSceneryHistoryBridge.mem_generated_iff_path δ (f Y)).mp
    exact (generated (IBMSceneryGaussianGerm.history δ)).starProjection_eq_self_iff.mp hY.symm
  · intro hm
    apply Lp.ext
    filter_upwards [(spatial δ).coeFn_compLpL f,hm] with Y hY hmY
    exact hY.trans ((generated (IBMSceneryGaussianGerm.history δ)).starProjection_eq_self_iff.mpr
      ((IBMSceneryHistoryBridge.mem_generated_iff_path δ (f Y)).mpr hmY))

theorem forecast_fixed_iff (δ : ℝ≥0) (F : JointL2) : forecast δ F = F ↔
    ∀ᵐ Y ∂gaussianProduct, AEStronglyMeasurable[IBMSpatialSceneryForecast.history δ]
      (sourceUnitary F Y) gaussianProduct := by
  rw [← field_fixed_iff]
  constructor
  · intro h
    have hh := congrArg sourceUnitary h
    simpa only [forecast,sourceUnitary.apply_symm_apply] using hh
  · intro h
    simp only [forecast,h,sourceUnitary.symm_apply_apply]

theorem field_inner (δ : ℝ≥0) (f g : ScalarFieldSpace) :
    inner ℝ (field δ f) g = inner ℝ f (field δ g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(spatial δ).coeFn_compLpL f,(spatial δ).coeFn_compLpL g] with Y hf hg
  change inner ℝ (field δ f Y) (g Y) = inner ℝ (f Y) (field δ g Y)
  change field δ f Y = spatial δ (f Y) at hf
  change field δ g Y = spatial δ (g Y) at hg
  rw [hf,hg]
  exact (generated (IBMSceneryGaussianGerm.history δ)).inner_starProjection_left_eq_right _ _

theorem forecast_inner (δ : ℝ≥0) (F G : JointL2) :
    inner ℝ (forecast δ F) G = inner ℝ F (forecast δ G) := by
  rw [← sourceUnitary.inner_map_map (forecast δ F) G,
    ← sourceUnitary.inner_map_map F (forecast δ G)]
  simpa only [forecast,sourceUnitary.apply_symm_apply] using
    field_inner δ (sourceUnitary F) (sourceUnitary G)

theorem forecast_pairing (δ : ℝ≥0) (F G : JointL2)
    (hG : ∀ᵐ Y ∂gaussianProduct, AEStronglyMeasurable[IBMSpatialSceneryForecast.history δ]
      (sourceUnitary G Y) gaussianProduct) :
    inner ℝ F G = inner ℝ (forecast δ F) G := by
  rw [forecast_inner, (forecast_fixed_iff δ G).mpr hG]


theorem forecast_continuous (δ : ℝ≥0) : Continuous (forecast δ) :=
  sourceUnitary.symm.continuous.comp ((field δ).continuous.comp sourceUnitary.continuous)

theorem sourceMean_eq_sourceVacuum (F : JointL2) :
    sourceMean F = IBMNativeSourceRecovery.sourceVacuum F := by
  unfold sourceMean IBMNativeSourceRecovery.sourceVacuum
  congr 1
  apply Lp.ext
  filter_upwards [vacuum_sections (sourceUnitary F),
    (GaussianNumberSectors.projection 0).coeFn_compLpL (sourceUnitary F)] with Y hm hp
  rw [hm,hp,GaussianNumberSectors.projection_zero]
  rfl

end OperatorDerivativeRewrite.Foundation.IBMJointSceneryForecast
