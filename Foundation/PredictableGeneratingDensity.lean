import Foundation.L2GeneratingIndicators
import Foundation.PredictableTimeTransport

/-! The actual predictable generators form a pi-system after adjoining univ.
Their indicators are dense in predictable L2 on every finite time horizon. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.PredictableGeneratingDensity
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 mΩ)

/-- Mathlib's actual predictable generators, with the harmless generator univ. -/
def generators : Set (Set (ℝ≥0 × Ω)) := insert univ
  ({s | ∃ A, MeasurableSet[𝓕 0] A ∧ s = {0} ×ˢ A} ∪
   {s | ∃ t A, MeasurableSet[𝓕 t] A ∧ s = Ioi t ×ˢ A})

theorem generators_generate : MeasurableSpace.generateFrom (generators 𝓕) = 𝓕.predictable := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro s (rfl | hs)
    · exact MeasurableSet.univ
    · exact MeasurableSpace.measurableSet_generateFrom hs
  · exact MeasurableSpace.generateFrom_mono (subset_insert _ _)

theorem generators_isPiSystem : IsPiSystem (generators 𝓕) := by
  apply IsPiSystem.insert_univ
  rintro s (⟨A, hA, rfl⟩ | ⟨a, A, hA, rfl⟩)
    t (⟨B, hB, rfl⟩ | ⟨b, B, hB, rfl⟩) hne
  · left
    refine ⟨A ∩ B, hA.inter hB, ?_⟩
    rw [prod_inter_prod, inter_self]
  · obtain ⟨z, hz0, hzb⟩ := hne
    have hz : z.1 = 0 := hz0.1
    have hb : b < z.1 := hzb.1
    rw [hz] at hb
    exact False.elim (not_lt_of_ge zero_le hb)
  · obtain ⟨z, hza, hz0⟩ := hne
    have hz : z.1 = 0 := hz0.1
    have ha : a < z.1 := hza.1
    rw [hz] at ha
    exact False.elim (not_lt_of_ge zero_le ha)
  · right
    refine ⟨max a b, A ∩ B,
      (𝓕.mono (le_max_left a b) _ hA).inter (𝓕.mono (le_max_right a b) _ hB), ?_⟩
    rw [prod_inter_prod, Ioi_inter_Ioi]

theorem predictable_le_product :
    𝓕.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (measurableSet_singleton 0).prod (𝓕.le 0 A hA)
  · intro s A hA
    exact measurableSet_Ioi.prod (𝓕.le s A hA)

/-- No predictable density is assumed: the generator density theorem is proved
by orthogonality, finite-measure integration and the pi-lambda argument. -/
theorem predictable_indicator_density (T : ℝ≥0) (μ : Measure Ω) [IsFiniteMeasure μ] :
    (generatingIndicatorSpan ((PredictableTimeTransport.timeMeasure T).prod μ)
      (generators 𝓕)).topologicalClosure =
      lpMeas ℝ ℝ 𝓕.predictable 2 ((PredictableTimeTransport.timeMeasure T).prod μ) :=
  generatingIndicatorSpan_closure _ (predictable_le_product 𝓕) _
    (generators_generate 𝓕) (generators_isPiSystem 𝓕) (mem_insert _ _)

end OperatorDerivativeRewrite.Foundation.PredictableGeneratingDensity
