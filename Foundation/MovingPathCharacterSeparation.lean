import Foundation.MovingPathCharacters
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! Separable uniform-norm sets contain only countably many positive-time evaluation characters. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.MovingPathCharacterSeparation
open MovingPathCharacters HigherHeatContinuousCylinders

theorem countable_times (S : Set ℝ) (hpos : ∀ t ∈ S, 0 < t)
    (hsep : IsSeparable (character '' S)) : S.Countable := by
  let g : S → (Path →ᵇ ℂ) := fun t => character t
  have hg : Function.Injective g := by
    intro s t he
    apply Subtype.ext
    by_contra hst
    have hd := character_dist s t (hpos s s.property) (hpos t t.property) hst
    change dist (g s) (g t) = 2 at hd
    rw [he, dist_self] at hd
    norm_num at hd
  have hr : IsSeparable (range g) := hsep.mono (by
    rintro _ ⟨t, rfl⟩
    exact ⟨t, t.property, rfl⟩)
  letI : SeparableSpace (range g) := hr.separableSpace
  have hd (x y : range g) (hne : x ≠ y) : dist x y = 2 := by
    obtain ⟨s, hs⟩ := x.property
    obtain ⟨t, ht⟩ := y.property
    have hst : (s : ℝ) ≠ (t : ℝ) := by
      intro he
      have he' : s = t := Subtype.ext he
      apply hne
      apply Subtype.ext
      rw [← hs, ← ht, he']
    change dist x.val y.val = 2
    rw [← hs, ← ht]
    exact character_dist s t (hpos s s.property) (hpos t t.property) hst
  letI : DiscreteTopology (range g) := by
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro x
    have he : Metric.ball x 1 = {x} := by
      ext y
      constructor
      · intro hy
        apply mem_singleton_iff.mpr
        by_contra hne
        have hh := hd y x hne
        have hb : dist y x < 1 := hy
        linarith
      · intro hy
        rcases mem_singleton_iff.mp hy with rfl
        simp
    rw [← he]
    exact Metric.isOpen_ball
  letI : Countable (range g) := separableSpace_iff_countable.mp inferInstance
  letI : Countable S := Function.Injective.countable
    (f := fun t : S => (⟨g t, mem_range_self t⟩ : range g))
    (fun s t he => hg (congrArg Subtype.val he))
  exact Set.to_countable S

theorem not_stronglyMeasurable : ¬ StronglyMeasurable character := by
  intro h
  have hs : IsSeparable (character '' Ioo (0 : ℝ) 1) :=
    h.isSeparable_range.mono (image_subset_range _ _)
  have hc := countable_times (Ioo (0 : ℝ) 1) (fun t ht => ht.1) hs
  have hz : volume (Ioo (0 : ℝ) 1) = 0 := hc.measure_zero volume
  simpa [Real.volume_Ioo] using hz

end OperatorDerivativeRewrite.Foundation.MovingPathCharacterSeparation
