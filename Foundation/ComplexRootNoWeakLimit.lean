import Foundation.ComplexRootNonTightness
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! No weak probability-law limit, even along any divergent refinement of the actual walks. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ComplexRootNoWeakLimit
open ComplexFourthRootWalk ComplexRootHeatTransformLimit ComplexRootNonTightness

def probabilityLaw (T : ℝ≥0) (n : ℕ) : ProbabilityMeasure ℂ :=
  (ComplexFourthRootWalk.law n (amplitude T n)).toProbabilityMeasure

theorem not_tight_reindexed (T : ℝ≥0) (hT : 0 < T) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) :
    ¬ IsTightMeasureSet (Set.range
      (fun n : ℕ => ComplexFourthRootWalk.law (φ n) (amplitude T (φ n)))) := by
  intro ht
  obtain ⟨K, hK, hμK⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (1/16) (by norm_num)
  obtain ⟨n, hn⟩ := (hφ.eventually (compact_escape T hT K hK)).exists
  have hu := ENNReal.toReal_mono (by norm_num : (1/16 : ℝ≥0∞) ≠ ⊤)
    (hμK _ ⟨n, rfl⟩)
  norm_num at hu
  change (ComplexFourthRootWalk.law (φ n) (amplitude T (φ n))).real Kᶜ ≤ 1/16 at hu
  linarith

theorem not_tendsto_reindexed (T : ℝ≥0) (hT : 0 < T) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) (μ : ProbabilityMeasure ℂ) :
    ¬ Tendsto (fun n => probabilityLaw T (φ n)) atTop (𝓝 μ) := by
  intro ht
  have hc := ht.isCompact_insert_range
  have hcl : IsCompact (closure (insert μ (Set.range (fun n => probabilityLaw T (φ n))))) := by
    rw [hc.isClosed.closure_eq]
    exact hc
  have hS := isTightMeasureSet_of_isCompact_closure hcl
  apply not_tight_reindexed T hT φ hφ
  apply hS.subset
  rintro ν ⟨n, rfl⟩
  exact ⟨probabilityLaw T (φ n), Set.mem_insert_of_mem μ ⟨n, rfl⟩, rfl⟩

theorem not_tendsto (T : ℝ≥0) (hT : 0 < T) (μ : ProbabilityMeasure ℂ) :
    ¬ Tendsto (probabilityLaw T) atTop (𝓝 μ) :=
  not_tendsto_reindexed T hT id tendsto_id μ

end OperatorDerivativeRewrite.Foundation.ComplexRootNoWeakLimit
