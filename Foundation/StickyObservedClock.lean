import Foundation.BrownianStickyOccupation
import Mathlib.MeasureTheory.Measure.Prod

/-! The inverse clock is an actual measurable functional of the observed sticky
path: elapsed physical time minus occupation of zero. No Markov law is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyObservedClock
open InfiniteGaussian BrownianMassRandomTimeChange BrownianStickyOccupation
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath
  BrownianMassRandomTimeChange.inverse BrownianRandomMassClock.mass

def holding (p : C(ℝ≥0, ℝ)) (T : ℝ≥0) : ℝ :=
  (volume {r : ℝ | 0 < r ∧ r ≤ (T : ℝ) ∧ p r.toNNReal = 0}).toReal

theorem holding_joint : Measurable (fun z : C(ℝ≥0, ℝ) × ℝ≥0 => holding z.1 z.2) := by
  have he : Measurable (fun z : (C(ℝ≥0, ℝ) × ℝ≥0) × ℝ => z.1.1 z.2.toNNReal) :=
    continuous_eval.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
      (continuous_real_toNNReal.measurable.comp measurable_snd))
  have ht : Measurable (fun z : (C(ℝ≥0, ℝ) × ℝ≥0) × ℝ => (z.1.2 : ℝ)) :=
    continuous_subtype_val.measurable.comp (measurable_snd.comp measurable_fst)
  have hs : MeasurableSet {z : (C(ℝ≥0, ℝ) × ℝ≥0) × ℝ |
      0 < z.2 ∧ z.2 ≤ (z.1.2 : ℝ) ∧ z.1.1 z.2.toNNReal = 0} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd ht).inter (measurableSet_eq_fun he measurable_const))
  exact (measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) hs).ennreal_toReal

theorem holding_nonnegative (p : C(ℝ≥0, ℝ)) (T : ℝ≥0) : 0 ≤ holding p T :=
  ENNReal.toReal_nonneg

theorem holding_congr_upto (p q : C(ℝ≥0, ℝ)) (T : ℝ≥0)
    (he : ∀ s ≤ T, p s = q s) : holding p T = holding q T := by
  unfold holding
  congr 2
  ext r
  simp only [mem_ofPred_eq]
  by_cases hr : r ≤ (T : ℝ)
  · rw [he r.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hr)]
  · simp only [hr,false_and,and_false]

theorem holding_le_time (p : C(ℝ≥0, ℝ)) (T : ℝ≥0) : holding p T ≤ T := by
  have hs : {r : ℝ | 0 < r ∧ r ≤ (T : ℝ) ∧ p r.toNNReal = 0} ⊆ Ioc 0 (T : ℝ) :=
    fun _ h => ⟨h.1,h.2.1⟩
  have hf : (volume : Measure ℝ) (Ioc 0 (T : ℝ)) ≠ ∞ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hm := ENNReal.toReal_mono hf (measure_mono hs)
  simpa only [holding,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal T.coe_nonneg] using hm

def inverseFromPath (p : C(ℝ≥0, ℝ)) (T : ℝ≥0) : ℝ≥0 :=
  ((T : ℝ)-holding p T).toNNReal

theorem inverseFromPath_joint :
    Measurable (fun z : C(ℝ≥0, ℝ) × ℝ≥0 => inverseFromPath z.1 z.2) :=
  continuous_real_toNNReal.measurable.comp
    ((continuous_subtype_val.measurable.comp measurable_snd).sub holding_joint)

theorem inverseFromPath_le (p : C(ℝ≥0, ℝ)) (T : ℝ≥0) : inverseFromPath p T ≤ T := by
  apply Real.toNNReal_le_iff_le_coe.mpr
  exact sub_le_self _ (holding_nonnegative p T)

theorem inverseFromPath_congr_upto (p q : C(ℝ≥0, ℝ)) (T : ℝ≥0)
    (he : ∀ s ≤ T, p s = q s) : inverseFromPath p T = inverseFromPath q T := by
  unfold inverseFromPath
  rw [holding_congr_upto p q T he]

theorem holding_actual : ∀ᵐ ω ∂gaussianProduct, ∀ κ T : ℝ≥0,
    holding (changedPath κ ω) T = (T : ℝ)-inverse κ ω T := by
  filter_upwards [zero_occupation_real] with ω hω κ T
  have hs : {r : ℝ | 0 < r ∧ r ≤ (T : ℝ) ∧ changedPath κ ω r.toNNReal = 0} =
      {r : ℝ | changedPath κ ω r.toNNReal = 0} ∩ Ioc 0 (T : ℝ) := by
    ext r
    simp only [mem_ofPred_eq,mem_inter_iff,mem_Ioc]
    tauto
  have hm : MeasurableSet {r : ℝ | changedPath κ ω r.toNNReal = 0} :=
    measurableSet_eq_fun ((changedPath κ ω).continuous.measurable.comp
      continuous_real_toNNReal.measurable) measurable_const
  unfold holding
  rw [hs,← Measure.restrict_apply hm,hω κ T,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (by exact_mod_cast inverse_le κ ω T))]

theorem inverse_recovery : ∀ᵐ ω ∂gaussianProduct, ∀ κ T : ℝ≥0,
    inverseFromPath (changedPath κ ω) T = inverse κ ω T := by
  filter_upwards [holding_actual] with ω hω κ T
  unfold inverseFromPath
  rw [hω κ T,sub_sub_cancel,Real.toNNReal_coe]

end OperatorDerivativeRewrite.Foundation.StickyObservedClock
