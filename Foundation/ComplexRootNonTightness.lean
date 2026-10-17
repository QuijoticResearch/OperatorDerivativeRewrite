import Foundation.ComplexRootScaledTail
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Analysis.Normed.Group.Bounded

/-! Failure of tightness for the genuine complex walk and polygonal path approximations. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ComplexRootNonTightness
open ComplexFourthRootWalk ComplexRootHeatTransformLimit ComplexRootScaledMoments
open ComplexRootScaledTail

theorem law_tail_mass_lower (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (hn : n ≠ 0)
    (b : ℝ) (hb : 0 ≤ b)
    (hbm : 2*b ≤ ∫ ω, ‖terminal n (amplitude T n) ω‖^2 ∂probability n) :
    1/8 ≤ (ComplexFourthRootWalk.law n (amplitude T n)).real {z | b < ‖z‖^2} := by
  have hA : MeasurableSet {z : ℂ | b < ‖z‖^2} :=
    measurableSet_lt measurable_const (by fun_prop)
  change 1/8 ≤ ((probability n).map (terminal n (amplitude T n)) {z | b < ‖z‖^2}).toReal
  rw [Measure.map_apply (terminal_measurable n (amplitude T n)) hA]
  exact tail_mass_lower T hT n hn b hb hbm

theorem compact_escape (T : ℝ≥0) (hT : 0 < T) (K : Set ℂ) (hK : IsCompact K) :
    ∀ᶠ n : ℕ in atTop, 1/8 ≤ (ComplexFourthRootWalk.law n (amplitude T n)).real Kᶜ := by
  obtain ⟨R, hR, hRK⟩ := hK.isBounded.exists_pos_norm_le
  have hm := (absolute_second_tendsto T hT).eventually (eventually_ge_atTop (2*R^2))
  filter_upwards [hm, eventually_ne_atTop (0 : ℕ)] with n hn hn0
  apply (law_tail_mass_lower T hT n hn0 (R^2) (sq_nonneg R) hn).trans
  apply measureReal_mono (μ := ComplexFourthRootWalk.law n (amplitude T n))
    ?_ (measure_ne_top _ _)
  intro z hz hzK
  have he := hRK z hzK
  have hz0 := norm_nonneg z
  have hz' : R^2 < ‖z‖^2 := hz
  nlinarith

theorem not_tight (T : ℝ≥0) (hT : 0 < T) :
    ¬ IsTightMeasureSet (Set.range (fun n : ℕ => ComplexFourthRootWalk.law n (amplitude T n))) := by
  intro ht
  obtain ⟨K, hK, hμK⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (1/16) (by norm_num)
  obtain ⟨n, hn⟩ := (compact_escape T hT K hK).exists
  have hu := ENNReal.toReal_mono (by norm_num : (1/16 : ℝ≥0∞) ≠ ⊤)
    (hμK _ ⟨n, rfl⟩)
  norm_num at hu
  change (ComplexFourthRootWalk.law n (amplitude T n)).real Kᶜ ≤ 1/16 at hu
  linarith

theorem not_path_tight (T : ℝ≥0) (hT : 0 < T) :
    ¬ IsTightMeasureSet (Set.range
      (fun n : ℕ => ComplexRootContinuousPaths.law n (amplitude T n))) := by
  intro ht
  have hc : Continuous (fun ω : ComplexRootContinuousPaths.Path => ω.val 1) :=
    (continuous_eval_const 1).comp continuous_subtype_val
  have he := ht.map hc
  rw [← Set.range_comp] at he
  apply not_tight T hT
  simpa only [Function.comp_def, ComplexRootContinuousPaths.terminal_law] using he

end OperatorDerivativeRewrite.Foundation.ComplexRootNonTightness
