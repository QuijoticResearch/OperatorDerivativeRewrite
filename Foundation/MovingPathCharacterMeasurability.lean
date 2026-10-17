import Foundation.MovingPathCharacterSeparation

/-! Moving evaluation characters have no Bochner Lp realization in the uniform path norm. -/
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology BoundedContinuousFunction NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.MovingPathCharacterMeasurability
open MovingPathCharacters MovingPathCharacterSeparation HigherHeatContinuousCylinders

def intervalMeasure : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

theorem not_aestronglyMeasurable : ¬ AEStronglyMeasurable character intervalMeasure := by
  intro h
  let f := h.mk character
  let S : Set ℝ := {t | t ∈ Ioo (0 : ℝ) 1 ∧ character t = f t}
  have hsep : IsSeparable (character '' S) := h.stronglyMeasurable_mk.isSeparable_range.mono (by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht.2.symm⟩)
  have hc : S.Countable := countable_times S (fun t ht => ht.1.1) hsep
  have hz : volume S = 0 := hc.measure_zero volume
  have hz' : intervalMeasure S = 0 :=
    le_antisymm ((Measure.restrict_apply_le (Ioo (0 : ℝ) 1) S).trans_eq hz) bot_le
  have hmem : ∀ᵐ t ∂intervalMeasure, t ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  have ha : ∀ᵐ t ∂intervalMeasure, t ∈ S := by
    filter_upwards [hmem, h.ae_eq_mk] with t ht he
    exact ⟨ht, he⟩
  have hnot : ∀ᵐ t ∂intervalMeasure, t ∉ S := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using hz'
  have hf : ∀ᵐ t ∂intervalMeasure, False := (ha.and hnot).mono (fun _ ht => ht.2 ht.1)
  have hzero : intervalMeasure univ = 0 := by
    simpa only [ae_iff, not_false_eq_true, setOf_true] using hf
  norm_num [intervalMeasure, Real.volume_Ioo] at hzero

theorem no_Lp_representative (p : ℝ≥0∞) (f : Lp (Path →ᵇ ℂ) p intervalMeasure) :
    ¬ (character =ᵐ[intervalMeasure] (f : ℝ → (Path →ᵇ ℂ))) := by
  intro he
  exact not_aestronglyMeasurable ((Lp.aestronglyMeasurable f).congr he.symm)

theorem nonzero_smul_not_aestronglyMeasurable (c : ℝ → ℂ) (hc : Measurable c)
    (hne : ∀ t, c t ≠ 0) :
    ¬ AEStronglyMeasurable (fun t => c t • character t) intervalMeasure := by
  intro h
  have hh := hc.inv.aestronglyMeasurable.smul h
  apply not_aestronglyMeasurable
  convert hh using 1
  funext t
  exact (inv_smul_smul₀ (hne t) (character t)).symm

end OperatorDerivativeRewrite.Foundation.MovingPathCharacterMeasurability
