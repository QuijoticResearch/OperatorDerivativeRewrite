import Foundation.ComplexRootPoissonTail
import Foundation.ComplexRootPoissonMarginals
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.Normed.Group.Bounded

/-! Actual Poissonized complex heat laws and their Markov trajectories fail tightness. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonNoWeakLimit
open ComplexRootHeatTransformLimit ComplexRootPoissonTail

def probabilityLaw (T : ℝ≥0) (n : ℕ) : ProbabilityMeasure ℂ :=
  (ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n)).toProbabilityMeasure

theorem compact_escape (T : ℝ≥0) (hT : 0 < T) (K : Set ℂ) (hK : IsCompact K) :
    ∀ᶠ n : ℕ in atTop,
      1/12 ≤ (ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n)).real Kᶜ := by
  obtain ⟨R, hR, hRK⟩ := hK.isBounded.exists_pos_norm_le
  have hm := (absolute_second_tendsto T hT).eventually (eventually_ge_atTop (2*R^2))
  filter_upwards [hm, eventually_ne_atTop (0 : ℕ)] with n hn hn0
  apply (tail_mass_lower T hT n hn0 (R^2) (sq_nonneg R) hn).trans
  apply measureReal_mono (μ := ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n))
    ?_ (measure_ne_top _ _)
  intro z hz hzK
  have he := hRK z hzK
  have hz0 := norm_nonneg z
  have hz' : R^2 < ‖z‖^2 := hz
  nlinarith

theorem not_tight_reindexed (T : ℝ≥0) (hT : 0 < T) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) :
    ¬ IsTightMeasureSet (Set.range
      (fun n : ℕ => ComplexRootPoissonLaw.law (φ n : ℝ≥0) (amplitude T (φ n)))) := by
  intro ht
  obtain ⟨K, hK, hμK⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (1/24) (by norm_num)
  obtain ⟨n, hn⟩ := (hφ.eventually (compact_escape T hT K hK)).exists
  have hu := ENNReal.toReal_mono (by norm_num : (1/24 : ℝ≥0∞) ≠ ⊤)
    (hμK _ ⟨n, rfl⟩)
  norm_num at hu
  change (ComplexRootPoissonLaw.law (φ n : ℝ≥0) (amplitude T (φ n))).real Kᶜ ≤ 1/24 at hu
  linarith

theorem not_tight (T : ℝ≥0) (hT : 0 < T) :
    ¬ IsTightMeasureSet (Set.range
      (fun n : ℕ => ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n))) :=
  not_tight_reindexed T hT id tendsto_id

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

theorem trajectory_coordinate_law (T : ℝ≥0) (n : ℕ) :
    (ComplexRootPoissonTrajectory.law (amplitude T n) (n : ℝ≥0)).map
      (ComplexRootPoissonTrajectory.coordinate 1) =
        ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n) := by
  rw [ComplexRootPoissonMarginals.marginal_kernel, one_nsmul, ComplexRootPoissonKernel.kernel_apply]
  simp only [zero_add]
  change (ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n)).map id = _
  exact Measure.map_id

theorem not_trajectory_tight (T : ℝ≥0) (hT : 0 < T) :
    ¬ IsTightMeasureSet (Set.range (fun n : ℕ =>
      ComplexRootPoissonTrajectory.law (amplitude T n) (n : ℝ≥0))) := by
  intro ht
  have hc : Continuous (ComplexRootPoissonTrajectory.coordinate 1) := continuous_apply 1
  have he := ht.map hc
  rw [← Set.range_comp] at he
  apply not_tight T hT
  simpa only [Function.comp_def, trajectory_coordinate_law] using he

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonNoWeakLimit
