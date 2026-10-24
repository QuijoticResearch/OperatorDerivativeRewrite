import Foundation.IBMSpatialIntegralTail
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Analysis.Normed.Group.Bounded

/-! The PARTICULAR actual joint mollified IBM integral has no ordinary
probability or weak-law limit. Compensated IBM convergence is preserved. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialIntegralNoProbabilityLimit
open IBMSpatialIntegralTail

def law (T : ℝ≥0) (r : ℕ) : Measure ℝ := IBMSourceLaws.jointMeasure.map (value r T)

instance law_probability (T : ℝ≥0) (r : ℕ) : IsProbabilityMeasure (law T r) := by
  unfold law
  infer_instance

def probabilityLaw (T : ℝ≥0) (r : ℕ) : ProbabilityMeasure ℝ := (law T r).toProbabilityMeasure

theorem law_tail_mass_lower (r : ℕ) (T : ℝ≥0) (hT : 0 < T) (b : ℝ) (hb : 0 ≤ b)
    (hbm : 2*b ≤ ∫ w, ‖value r T w‖^2 ∂IBMSourceLaws.jointMeasure) :
    1/36 ≤ (law T r).real {z | b < ‖z‖^2} := by
  have hA : MeasurableSet {z : ℝ | b < ‖z‖^2} := measurableSet_lt measurable_const (by fun_prop)
  change 1/36 ≤ (IBMSourceLaws.jointMeasure.map (value r T) {z | b < ‖z‖^2}).toReal
  rw [Measure.map_apply (Lp.stronglyMeasurable _).measurable hA]
  exact tail_mass_lower r T hT b hb hbm

theorem compact_escape (T : ℝ≥0) (hT : 0 < T) (K : Set ℝ) (hK : IsCompact K) :
    ∀ᶠ r : ℕ in atTop, 1/36 ≤ (law T r).real Kᶜ := by
  obtain ⟨R, _hR, hRK⟩ := hK.isBounded.exists_pos_norm_le
  have hm := (second_tendsto T hT).eventually (eventually_ge_atTop (2*R^2))
  filter_upwards [hm] with r hr
  apply (law_tail_mass_lower r T hT (R^2) (sq_nonneg R) hr).trans
  apply measureReal_mono (μ := law T r) ?_ (measure_ne_top _ _)
  intro z hz hzK
  have he := hRK z hzK
  have hz' : R^2 < ‖z‖^2 := hz
  nlinarith [norm_nonneg z]

theorem not_tight_reindexed (T : ℝ≥0) (hT : 0 < T) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) :
    ¬ IsTightMeasureSet (Set.range (fun n => law T (φ n))) := by
  intro ht
  obtain ⟨K, hK, hμK⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (1/72) (by norm_num)
  obtain ⟨n, hn⟩ := (hφ.eventually (compact_escape T hT K hK)).exists
  have hu := ENNReal.toReal_mono (by norm_num : (1/72 : ℝ≥0∞) ≠ ⊤)
    (hμK _ ⟨n, rfl⟩)
  norm_num at hu
  change (law T (φ n)).real Kᶜ ≤ 1/72 at hu
  linarith

theorem not_tight (T : ℝ≥0) (hT : 0 < T) :
    ¬ IsTightMeasureSet (Set.range (law T)) := not_tight_reindexed T hT id tendsto_id

theorem not_tendsto_reindexed (T : ℝ≥0) (hT : 0 < T) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) (μ : ProbabilityMeasure ℝ) :
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

theorem not_tendstoInMeasure_reindexed (T : ℝ≥0) (hT : 0 < T) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) (F : IBMSourceLaws.JointSample → ℝ) :
    ¬ TendstoInMeasure IBMSourceLaws.jointMeasure (fun n => value (φ n) T) atTop F := by
  intro h
  have hd := h.tendstoInDistribution (fun n => (Lp.stronglyMeasurable (value (φ n) T)).measurable.aemeasurable)
  exact not_tendsto_reindexed T hT φ hφ
    ⟨IBMSourceLaws.jointMeasure.map F, inferInstance⟩ hd.tendsto

theorem not_tendstoInMeasure (T : ℝ≥0) (hT : 0 < T) (F : IBMSourceLaws.JointSample → ℝ) :
    ¬ TendstoInMeasure IBMSourceLaws.jointMeasure (fun r => value r T) atTop F :=
  not_tendstoInMeasure_reindexed T hT id tendsto_id F

end OperatorDerivativeRewrite.Foundation.IBMSpatialIntegralNoProbabilityLimit
