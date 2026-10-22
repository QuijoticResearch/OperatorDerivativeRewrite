import Foundation.IBMSpatialSceneryForecast

/-! A genuine spatially clipped IBM process and its vanishing L2 forecast bound.
No initial-germ identification is asserted here. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClippedSceneryForecast
open InfiniteGaussian IBMConstructedSources IBMContinuousScenery IBMRandomTimeHilbert
open IBMTimeAveragedObservable
set_option backward.isDefEq.respectTransparency false

def sourceSlice (t δ : ℝ≥0) (ω : SampleSpace) : GaussianL2 :=
  sourceScenery (min |GaussianTimeProcess.process t ω| (δ : ℝ))

theorem slice_measurable (t δ : ℝ≥0) : StronglyMeasurable (sourceSlice t δ) :=
  sourceScenery_continuous.stronglyMeasurable.comp_measurable
    ((continuous_abs.measurable.comp
      (GaussianTimeProcess.process_stronglyMeasurable t).measurable).min measurable_const)

theorem slice_bound (t δ : ℝ≥0) (ω : SampleSpace) : ‖sourceSlice t δ ω‖ ≤ Real.sqrt δ := by
  have hn : ‖sourceSlice t δ ω‖ ^ 2 ≤ (δ : ℝ) := by
    rw [sourceSlice, sourceScenery_norm_sq, abs_of_nonneg (le_min (abs_nonneg _) δ.coe_nonneg)]
    exact min_le_right _ _
  nlinarith [Real.sq_sqrt δ.coe_nonneg, Real.sqrt_nonneg (δ : ℝ), norm_nonneg (sourceSlice t δ ω)]

theorem slice_projection (t δ : ℝ≥0) (ω : SampleSpace) :
    (condExpL2 ℝ ℝ (IBMSpatialSceneryForecast.history.le δ) (randomSourceClass t ω) : GaussianL2) =
      sourceSlice t δ ω :=
  IBMSpatialSceneryForecast.prediction_class δ
    (⟨|GaussianTimeProcess.process t ω|, abs_nonneg _⟩ : ℝ≥0)

theorem slice_memLp (t δ : ℝ≥0) : MemLp (sourceSlice t δ) 2 gaussianProduct :=
  MemLp.of_bound (slice_measurable t δ).aestronglyMeasurable (Real.sqrt δ)
    (ae_of_all _ (slice_bound t δ))

def field (t δ : ℝ≥0) : ValueSpace := (slice_memLp t δ).toLp _

theorem field_ae (t δ : ℝ≥0) : field t δ =ᵐ[gaussianProduct] sourceSlice t δ :=
  (slice_memLp t δ).coeFn_toLp

def forecast (t δ : ℝ≥0) : JointL2 := jointRealization (field t δ)

theorem forecast_bound (t δ : ℝ≥0) : ‖forecast t δ‖ ≤ Real.sqrt δ := by
  have hb : ∀ᵐ ω ∂gaussianProduct, ‖field t δ ω‖ ≤ Real.sqrt δ := by
    filter_upwards [field_ae t δ] with ω hω
    rw [hω]
    exact slice_bound t δ ω
  have hn := Lp.norm_le_of_ae_bound (Real.sqrt_nonneg (δ : ℝ)) hb
  rw [forecast, jointRealization.norm_map]
  simpa [measureUnivNNReal] using hn

def actualValue (δ t : ℝ≥0) (ω : IBMSourceLaws.JointSample) : ℝ :=
  sceneryPath ω.1 (min |clockPath ω.2 t| (δ : ℝ))

theorem actual_continuous (δ : ℝ≥0) (ω : IBMSourceLaws.JointSample) :
    Continuous (fun t => actualValue δ t ω) :=
  (sceneryPath ω.1).continuous.comp (((clockPath ω.2).continuous.abs).min continuous_const)

theorem actual_measurable (δ t : ℝ≥0) : Measurable (actualValue δ t) := by
  have hX : Measurable (fun ω : IBMSourceLaws.JointSample => sceneryPath ω.1) :=
    sceneryPath_measurable.comp measurable_fst
  have hY : Measurable (fun ω : IBMSourceLaws.JointSample =>
      min |clockPath ω.2 t| (δ : ℝ)) := (continuous_abs.measurable.comp
    ((ContinuousMap.measurable_eval t).comp (clockPath_measurable.comp measurable_snd))).min
      (measurable_const (a := (δ : ℝ)))
  exact continuous_eval.measurable.comp (hX.prodMk hY)

theorem actual_jointly_measurable (δ : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × IBMSourceLaws.JointSample => actualValue δ p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable (actual_continuous δ) (actual_measurable δ)

theorem slice_actual_ae (t δ : ℝ≥0) : ∀ᵐ ωY ∂gaussianProduct,
    sourceSlice t δ ωY =ᵐ[gaussianProduct] fun ωX => actualValue δ t (ωX, ωY) := by
  filter_upwards [clockPath_coordinate_ae t] with ωY hy
  filter_upwards [sceneryPath_coordinate_ae
    (min |GaussianTimeProcess.process t ωY| (δ : ℝ))] with ωX hx
  change sourceScenery (min |GaussianTimeProcess.process t ωY| (δ : ℝ)) ωX =
    sceneryPath ωX (min |clockPath ωY t| (δ : ℝ))
  rw [hy, hx]
  rfl

theorem forecast_actual_ae (t δ : ℝ≥0) :
    forecast t δ =ᵐ[IBMSourceLaws.jointMeasure] actualValue δ t := by
  apply jointRealization_ae_of_sections _ _ (actual_measurable δ t)
  filter_upwards [field_ae t δ, slice_actual_ae t δ] with ωY hf hs
  rw [hf]
  exact hs

theorem actual_section_prediction (t δ : ℝ≥0) : ∀ᵐ ωY ∂gaussianProduct,
    gaussianProduct[fun ωX => ibmValue t (ωX,ωY) | IBMSpatialSceneryForecast.history δ]
      =ᵐ[gaussianProduct] fun ωX => actualValue δ t (ωX,ωY) := by
  filter_upwards [IBMUnmollifiedSourceDerivative.actual_section_ae t, slice_actual_ae t δ]
    with ωY ho hc
  have he : (condExpL2 ℝ ℝ (IBMSpatialSceneryForecast.history.le δ)
      (randomSourceClass t ωY) : GaussianL2) =ᵐ[gaussianProduct]
        gaussianProduct[randomSourceClass t ωY | IBMSpatialSceneryForecast.history δ] := by
    simpa only [Lp.toLp_coeFn] using
      (Lp.memLp (randomSourceClass t ωY)).condExpL2_ae_eq_condExp
        (𝕜 := ℝ) (IBMSpatialSceneryForecast.history.le δ)
  rw [slice_projection] at he
  exact (condExp_congr_ae ho).trans (he.symm.trans hc)

theorem actual_memLp (δ t : ℝ≥0) : MemLp (actualValue δ t) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (forecast t δ)).ae_eq (forecast_actual_ae t δ)

theorem spatial_past_measurable (δ t : ℝ≥0) (ωY : SampleSpace) :
    Measurable[IBMSpatialSceneryForecast.history δ]
      (fun ωX => actualValue δ t (ωX,ωY)) := by
  let r : ℝ≥0 := min ⟨|clockPath ωY t|, abs_nonneg _⟩ δ
  have hm := (IBMSpatialSceneryForecast.scenery_adapted r).mono
    (IBMSpatialSceneryForecast.history.mono (min_le_right _ _))
  have hh := hm.measurable
  change Measurable[IBMSpatialSceneryForecast.history δ]
    (fun ωX => sceneryPath ωX (r : ℝ)) at hh
  have he : (fun ωX => sceneryPath ωX (r : ℝ)) =
      (fun ωX => actualValue δ t (ωX,ωY)) := by
    funext ωX
    change sceneryPath ωX ((min (⟨|clockPath ωY t|, abs_nonneg _⟩ : ℝ≥0) δ : ℝ≥0) : ℝ) = _
    rw [NNReal.coe_min]
    rfl
  exact he ▸ hh

theorem past_functional_spatial_measurable (δ T : ℝ≥0)
    (g : (Iic T → ℝ) → ℝ) (hg : Measurable g) (ωY : SampleSpace) :
    Measurable[IBMSpatialSceneryForecast.history δ] (fun ωX =>
      GaussianPredictableStep.pastCoefficient (actualValue δ) T g (ωX,ωY)) := by
  let : MeasurableSpace SampleSpace := IBMSpatialSceneryForecast.history δ
  exact hg.comp (Measurable.of_eval fun r => spatial_past_measurable δ r ωY)

theorem actual_eq_ibm (δ t : ℝ≥0) (ω : IBMSourceLaws.JointSample)
    (hclock : |clockPath ω.2 t| ≤ (δ : ℝ)) : actualValue δ t ω = ibmValue t ω := by
  rw [actualValue, min_eq_left hclock, ibmValue_eq]

theorem actual_past_eq (δ T : ℝ≥0) (ω : IBMSourceLaws.JointSample)
    (hclock : ∀ t ≤ T, |clockPath ω.2 t| ≤ (δ : ℝ)) :
    ∀ t ≤ T, actualValue δ t ω = ibmValue t ω :=
  fun t ht => actual_eq_ibm δ t ω (hclock t ht)

theorem forecast_tendsto_zero (t : ℝ≥0) (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => forecast t (δ n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hr : Tendsto (fun n => Real.sqrt (δ n : ℝ)) atTop (𝓝 0) := by
    have hδr : Tendsto (fun n => (δ n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).comp hδ
    have hs : Tendsto (fun n => Real.sqrt (δ n : ℝ)) atTop (𝓝 (Real.sqrt (0 : ℝ))) :=
      (Real.continuous_sqrt.tendsto 0).comp hδr
    simpa only [Real.sqrt_zero] using hs
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => forecast_bound t (δ n)) hr

end OperatorDerivativeRewrite.Foundation.IBMClippedSceneryForecast
