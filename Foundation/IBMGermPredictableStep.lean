import Foundation.IBMObservedInitialGerm

/-! Actual raw-past bounded steps for the existing right-germ terminal channel. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMGermPredictableStep
open IBMTimeAveragedObservable IBMIntrinsicRightGerm IBMObservedTerminalMartingale
open IBMWeightedTerminalEnergy IBMRightGermFiltration
open IBMIntrinsicMartingaleStep (Coefficient)
set_option backward.isDefEq.respectTransparency false

def stepClass (F : JointL2) (s t : ℝ≥0) (a : Coefficient s) : JointL2 :=
  channelClass (weightedTerminal F s a) t - channelClass (weightedTerminal F s a) s

theorem stepClass_ae (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    stepClass F s t a =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a.function ω * (channel F t ω - channel F s ω) := by
  filter_upwards [Lp.coeFn_sub (channelClass (weightedTerminal F s a) t)
    (channelClass (weightedTerminal F s a) s), weighted_channel F s a hst,
    weighted_channel F s a le_rfl] with ω he ht hs
  change stepClass F s t a ω = _ at he ⊢
  rw [he]
  change channel (weightedTerminal F s a) t ω - channel (weightedTerminal F s a) s ω = _
  rw [ht, hs]
  simp only [Pi.mul_apply]
  ring

theorem stepClass_mem_rightPast (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (a : Coefficient s) : stepClass F s t a ∈ rightPast t :=
  (rightPast t).sub_mem (Submodule.starProjection_apply_mem _ _)
    (rightPast_mono hst (Submodule.starProjection_apply_mem _ _))

theorem stepClass_projection_zero (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (a : Coefficient s) : (rightPast s).starProjection (stepClass F s t a) = 0 := by
  rw [stepClass, map_sub, project_channel _ hst, project_channel _ le_rfl, sub_self]

theorem past_inner_step_zero (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (a : Coefficient s) (g : JointL2) (hg : g ∈ rightPast s) :
    inner ℝ g (stepClass F s t a) = 0 := by
  have he := (rightPast s).inner_starProjection_left_eq_right g (stepClass F s t a)
  rw [Submodule.starProjection_eq_self_iff.mpr hg, stepClass_projection_zero F hst a,
    inner_zero_right] at he
  exact he

theorem disjoint_steps_orthogonal (F : JointL2) {r u s t : ℝ≥0}
    (hru : r ≤ u) (hus : u ≤ s) (hst : s ≤ t) (a : Coefficient r) (b : Coefficient s) :
    inner ℝ (stepClass F r u a) (stepClass F s t b) = 0 :=
  past_inner_step_zero F hst b _
    (rightPast_mono hus (stepClass_mem_rightPast F hru a))

theorem step_energy (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    ‖stepClass F s t a‖ ^ 2 =
      ∫ ω, a.function ω ^ 2 * (channel F t ω - channel F s ω) ^ 2
        ∂IBMSourceLaws.jointMeasure :=
  weighted_increment_norm F s a le_rfl hst

theorem terminal_pairing (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    inner ℝ F (stepClass F s t a) =
      ∫ ω, a.function ω * (channel F t ω - channel F s ω) ^ 2
        ∂IBMSourceLaws.jointMeasure := by
  have hp := (rightPast t).starProjection_inner_eq_zero F _ (stepClass_mem_rightPast F hst a)
  have ho := past_inner_step_zero F hst a (channelClass F s)
    (Submodule.starProjection_apply_mem _ _)
  have he : inner ℝ F (stepClass F s t a) =
      inner ℝ (channelClass F t - channelClass F s) (stepClass F s t a) := by
    change inner ℝ (F - channelClass F t) (stepClass F s t a) = 0 at hp
    rw [inner_sub_left] at hp ⊢
    linarith
  rw [he, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (channelClass F t) (channelClass F s), stepClass_ae F hst a]
    with ω hd hs
  rw [hd, hs, Real.inner_apply]
  change (channel F t ω - channel F s ω) *
    (a.function ω * (channel F t ω - channel F s ω)) = _
  ring

theorem idempotent_pairing (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s)
    (ha : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, a.function ω ^ 2 = a.function ω) :
    inner ℝ F (stepClass F s t a) = ‖stepClass F s t a‖ ^ 2 := by
  rw [terminal_pairing F hst a, step_energy F hst a]
  apply integral_congr_ae
  filter_upwards [ha] with ω hω
  rw [hω]

theorem stepClass_self (F : JointL2) (s : ℝ≥0) (a : Coefficient s) :
    stepClass F s s a = 0 := by
  rw [stepClass, sub_self]

end OperatorDerivativeRewrite.Foundation.IBMGermPredictableStep
