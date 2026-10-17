import Foundation.AmbientNullAugmentation
import Mathlib.MeasureTheory.Constructions.Pi

/-! Coordinate modifications generate the same ambient-null-augmented
observation sigma-algebra, including uncountable observation families. -/
noncomputable section
open MeasureTheory Set Filter
namespace OperatorDerivativeRewrite.Foundation.ObservationModificationAugmentation
set_option backward.isDefEq.respectTransparency false
open AmbientNullAugmentation
variable {Ω I : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)

@[instance_reducible] def observationSpace (f : I → Ω → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω i => f i ω) inferInstance

theorem coordinate_measurable (f : I → Ω → ℝ) (i : I) :
    Measurable[observationSpace f] (f i) :=
  (measurable_pi_apply i).comp (comap_measurable (fun ω i => f i ω))

theorem observationSpace_le (f : I → Ω → ℝ) (hf : ∀ i, Measurable (f i)) :
    observationSpace f ≤ m₀ := (Measurable.of_eval hf).comap_le

theorem augment_idempotent (m : MeasurableSpace Ω) :
    augment (m₀ := m₀) (augment (m₀ := m₀) m μ) μ = augment (m₀ := m₀) m μ := by
  letI : MeasurableSpace Ω := m₀
  apply le_antisymm
  · intro s hs
    obtain ⟨hs,A,hA,he⟩ := hs
    obtain ⟨_,B,hB,hAB⟩ := hA
    refine ⟨hs,B,hB,?_⟩
    filter_upwards [he,hAB] with ω hω hω'
    exact hω.trans hω'
  · exact raw_le _ μ (le_ambient m μ)

theorem observationSpace_le_augmented (f g : I → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (he : ∀ i, f i =ᵐ[μ] g i) :
    observationSpace f ≤ augment (observationSpace g) μ := by
  have hm : @Measurable Ω (I → ℝ) (augment (observationSpace g) μ) inferInstance
      (fun ω i => f i ω) := by
    letI : MeasurableSpace Ω := augment (m₀ := m₀) (observationSpace g) μ
    exact Measurable.of_eval (fun i =>
      measurable_of_raw_aestronglyMeasurable (m₀ := m₀) (observationSpace g) μ (hf i)
        ((coordinate_measurable g i).stronglyMeasurable.aestronglyMeasurable.congr (he i).symm))
  exact hm.comap_le

theorem augmented_observationSpace_eq (f g : I → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (he : ∀ i, f i =ᵐ[μ] g i) :
    augment (observationSpace f) μ = augment (observationSpace g) μ := by
  apply le_antisymm
  · have h := monotone μ (observationSpace_le_augmented μ f g hf he)
    dsimp only at h
    rwa [augment_idempotent] at h
  · have h := monotone μ (observationSpace_le_augmented μ g f hg (fun i => (he i).symm))
    dsimp only at h
    rwa [augment_idempotent] at h

theorem condExp_observation_eq [IsFiniteMeasure μ] (f g : I → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (he : ∀ i, f i =ᵐ[μ] g i) (F : Ω → ℝ) (hF : Integrable F μ) :
    μ[F | observationSpace f] =ᵐ[μ] μ[F | observationSpace g] := by
  calc
    _ =ᵐ[μ] μ[F | augment (observationSpace f) μ] :=
      condExp_invariant _ μ (observationSpace_le f hf) F hF
    _ =ᵐ[μ] μ[F | augment (observationSpace g) μ] := by
      rw [augmented_observationSpace_eq μ f g hf hg he]
    _ =ᵐ[μ] _ := (condExp_invariant _ μ (observationSpace_le g hg) F hF).symm

end OperatorDerivativeRewrite.Foundation.ObservationModificationAugmentation
