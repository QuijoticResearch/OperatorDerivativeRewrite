import Foundation.IBMIntrinsicRightGerm
import Foundation.IBMIntrinsicOriginContinuity
import Mathlib.Analysis.SpecificLimits.Basic

/-! A concrete right approach realizes every intrinsic IBM L2 germ and retains
the sharp quadratic energy bound. No zero-jump assertion is imposed at positive time. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicRightApproach
open IBMIntrinsicRightGerm IBMIntrinsicQuadraticMartingale IBMTimeAveragedObservable
set_option backward.isDefEq.respectTransparency false

def approach (t : ℝ≥0) (n : ℕ) : ℝ≥0 := t + (1 / 2) ^ n

theorem approach_positive (t : ℝ≥0) (n : ℕ) : t < approach t n :=
  lt_add_of_pos_right t (pow_pos (by norm_num) n)

theorem approach_bound (t : ℝ≥0) (n : ℕ) : approach t n ≤ t + 1 := by
  unfold approach
  exact add_le_add le_rfl (pow_le_one₀ (by norm_num : 0 ≤ (1 / 2 : ℝ≥0)) (by norm_num))

theorem approach_antitone (t : ℝ≥0) : Antitone (approach t) := by
  intro i j hij
  change t + (1 / 2) ^ j ≤ t + (1 / 2) ^ i
  exact add_le_add le_rfl (pow_le_pow_right_of_le_one' (by norm_num : (1 / 2 : ℝ≥0) ≤ 1) hij)

theorem approach_tendsto (t : ℝ≥0) : Tendsto (approach t) atTop (𝓝 t) := by
  change Tendsto (fun n : ℕ => t + (1 / 2) ^ n) atTop (𝓝 t)
  have ht : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
  simpa only [add_zero] using ht.add
    (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0) < 1))

theorem approach_valueClass_tendsto (t : ℝ≥0) :
    Tendsto (fun n => (valueClass (approach t n) : JointL2)) atTop (𝓝 (rightLimitClass t)) :=
  valueClass_tendsto_right (approach t) (approach_antitone t) t (t + 1)
    (approach_positive t) (approach_bound t) (approach_tendsto t)

theorem rightLimitClass_bound (t : ℝ≥0) : ‖rightLimitClass t‖ ^ 2 ≤ 2 * (t : ℝ) ^ 2 := by
  have hv := (approach_valueClass_tendsto t).norm.pow 2
  have ht := (((NNReal.continuous_coe.tendsto t).comp (approach_tendsto t)).pow 2).const_mul (2 : ℝ)
  apply le_of_tendsto_of_tendsto hv ht
  exact Eventually.of_forall fun n => valueClass_bound_sq (approach t n)

theorem jumpClass_energy_bound (t : ℝ≥0) :
    ‖jumpClass t‖ ^ 2 ≤ 2 * (t : ℝ) ^ 2 - ‖(valueClass t : JointL2)‖ ^ 2 := by
  have he := energy_decomposition t
  have hb := rightLimitClass_bound t
  linarith

theorem rightLimitClass_zero : rightLimitClass 0 = 0 := by
  have hb := rightLimitClass_bound 0
  norm_num at hb
  exact hb

theorem jumpClass_zero : jumpClass 0 = 0 := by
  have he := project_to_present 0
  rw [rightLimitClass_zero, map_zero] at he
  unfold jumpClass
  rw [rightLimitClass_zero, ← he, sub_self]

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicRightApproach
