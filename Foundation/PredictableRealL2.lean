import Foundation.PredictableGeneratingDensity
import Foundation.L2ZeroExtension

/-! Predictable measurable subspaces in the existing real-time representation.
Negative times are collapsed to zero only for the sigma-algebra; horizon
restriction and zero extension impose the actual time support separately. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.PredictableRealL2
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def toNonnegative (z : ℝ × Ω) : ℝ≥0 × Ω := (z.1.toNNReal, z.2)

theorem toNonnegative_measurable : Measurable (toNonnegative (Ω := Ω)) :=
  (measurable_fst.real_toNNReal).prodMk measurable_snd

@[instance_reducible]
def predictable (𝓕 : Filtration ℝ≥0 mΩ) : MeasurableSpace (ℝ × Ω) :=
  MeasurableSpace.comap toNonnegative 𝓕.predictable

theorem predictable_le (𝓕 : Filtration ℝ≥0 mΩ) :
    predictable 𝓕 ≤ (inferInstance : MeasurableSpace (ℝ × Ω)) :=
  (MeasurableSpace.comap_mono (PredictableGeneratingDensity.predictable_le_product 𝓕)).trans
    toNonnegative_measurable.comap_le

def generators (𝓕 : Filtration ℝ≥0 mΩ) : Set (Set (ℝ × Ω)) :=
  (Set.preimage toNonnegative) '' PredictableGeneratingDensity.generators 𝓕

theorem generators_generate (𝓕 : Filtration ℝ≥0 mΩ) :
    MeasurableSpace.generateFrom (generators 𝓕) = predictable 𝓕 := by
  rw [predictable, ← PredictableGeneratingDensity.generators_generate,
    MeasurableSpace.comap_generateFrom]
  rfl

theorem generators_isPiSystem (𝓕 : Filtration ℝ≥0 mΩ) : IsPiSystem (generators 𝓕) :=
  (PredictableGeneratingDensity.generators_isPiSystem 𝓕).comap toNonnegative

def horizon (T : ℝ≥0) : Set (ℝ × Ω) := Ioc 0 (T : ℝ) ×ˢ univ

theorem horizon_measurable (T : ℝ≥0) : MeasurableSet (horizon (Ω := Ω) T) :=
  measurableSet_Ioc.prod MeasurableSet.univ

abbrev horizonMeasure (T : ℝ≥0) (μ : Measure Ω) : Measure (ℝ × Ω) :=
  ((volume : Measure ℝ).prod μ).restrict (horizon T)

theorem horizonMeasure_eq_product (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ] :
    horizonMeasure T μ = ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))).prod μ := by
  simpa only [horizonMeasure, horizon, Measure.restrict_univ] using
    (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := μ) (Ioc 0 (T : ℝ)) univ).symm

instance horizonMeasure_finite (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ] :
    IsFiniteMeasure (horizonMeasure T μ) := by
  rw [horizonMeasure_eq_product]
  infer_instance

theorem horizonMeasure_eq_closed (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ] :
    horizonMeasure T μ = ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).prod μ := by
  rw [horizonMeasure_eq_product,
    Measure.restrict_congr_set (Ioc_ae_eq_Icc' (measure_singleton (0 : ℝ)))]

omit [MeasurableSpace Ω] in
theorem horizon_inter_zero (T : ℝ≥0) (A : Set Ω) :
    horizon T ∩ toNonnegative ⁻¹' ({0} ×ˢ A) = ∅ := by
  ext z
  simp only [horizon, toNonnegative, mem_inter_iff, mem_prod, mem_Ioc, mem_univ,
    and_true, mem_preimage, mem_singleton_iff, Real.toNNReal_eq_zero, mem_empty_iff_false,
    iff_false, not_and]
  intro hz hz0
  exact False.elim ((not_le_of_gt hz.1) hz0)

omit [MeasurableSpace Ω] in
theorem horizon_inter_Ioi (T s : ℝ≥0) (A : Set Ω) :
    horizon T ∩ toNonnegative ⁻¹' (Ioi s ×ˢ A) = Ioc (s : ℝ) (T : ℝ) ×ˢ A := by
  ext z
  simp only [horizon, toNonnegative, mem_inter_iff, mem_prod, mem_Ioc, mem_univ,
    and_true, mem_preimage, mem_Ioi, Real.lt_toNNReal_iff_coe_lt]
  constructor
  · rintro ⟨⟨_, ht⟩, hs, ha⟩
    exact ⟨⟨hs, ht⟩, ha⟩
  · rintro ⟨⟨hs, ht⟩, ha⟩
    exact ⟨⟨lt_of_le_of_lt s.coe_nonneg hs, ht⟩, hs, ha⟩

theorem indicator_density (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    (generatingIndicatorSpan (horizonMeasure T μ) (generators 𝓕)).topologicalClosure =
      lpMeas ℝ ℝ (predictable 𝓕) 2 (horizonMeasure T μ) := by
  apply generatingIndicatorSpan_closure _ (predictable_le 𝓕) _
    (generators_generate 𝓕) (generators_isPiSystem 𝓕)
  exact ⟨univ, mem_insert _ _, preimage_univ⟩

theorem coeTime_measurePreserving (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ] :
    MeasurePreserving PredictableTimeTransport.coeTime
      ((PredictableTimeTransport.timeMeasure T).prod μ) (horizonMeasure T μ) := by
  rw [horizonMeasure_eq_closed]
  exact PredictableTimeTransport.coeTime_measurePreserving T μ

theorem toNonnegative_measurePreserving (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ] :
    MeasurePreserving toNonnegative (horizonMeasure T μ)
      ((PredictableTimeTransport.timeMeasure T).prod μ) := by
  refine ⟨toNonnegative_measurable, ?_⟩
  rw [← (coeTime_measurePreserving T μ).map_eq,
    Measure.map_map toNonnegative_measurable
      PredictableTimeTransport.coeTime_measurableEmbedding.measurable]
  have he : toNonnegative ∘ (PredictableTimeTransport.coeTime (Ω := Ω)) = id := by
    funext z
    simp [toNonnegative, PredictableTimeTransport.coeTime]
  rw [he, Measure.map_id]

def nonnegativePullback (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Lp ℝ 2 ((PredictableTimeTransport.timeMeasure T).prod μ) →ₗᵢ[ℝ]
      Lp ℝ 2 (horizonMeasure T μ) :=
  Lp.compMeasurePreservingₗᵢ ℝ toNonnegative (toNonnegative_measurePreserving T μ)

theorem nonnegativePullback_predictable (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Lp ℝ 2 ((PredictableTimeTransport.timeMeasure T).prod μ))
    (hF : AEStronglyMeasurable[𝓕.predictable] F ((PredictableTimeTransport.timeMeasure T).prod μ)) :
    AEStronglyMeasurable[predictable 𝓕] (nonnegativePullback T μ F) (horizonMeasure T μ) := by
  have hm : StronglyMeasurable[predictable 𝓕] (hF.mk F ∘ toNonnegative) :=
    hF.stronglyMeasurable_mk.comp_measurable (Measurable.of_comap_le le_rfl)
  exact hm.aestronglyMeasurable.congr
    ((Lp.coeFn_compMeasurePreserving F (toNonnegative_measurePreserving T μ)).trans
      ((toNonnegative_measurePreserving T μ).quasiMeasurePreserving.ae_eq_comp hF.ae_eq_mk)).symm

end OperatorDerivativeRewrite.Foundation.PredictableRealL2
