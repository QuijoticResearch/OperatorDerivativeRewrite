import Foundation.IBMTerminalPredictableGrid

/-! Uniform actual stochastic energy for fixed-terminal IBM martingales.
The bound uses the terminal L2 norm, with no deterministic time horizon. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTerminalIntegralEnergy
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction IBMRawObservedMartingale
open IBMIntrinsicMartingaleStep (Coefficient)
open IBMIntrinsicMartingaleRefinement (constant)
open IBMTerminalPredictableStep IBMTerminalPredictableGrid
set_option backward.isDefEq.respectTransparency false

theorem unit_stepClass (F : JointL2) (s t : ℝ≥0) :
    stepClass F s t (constant s 1) = rawClass F t - rawClass F s := by
  apply Lp.ext
  filter_upwards [stepClass_ae F s t (constant s 1), rawClass_ae F t, rawClass_ae F s,
    Lp.coeFn_sub (rawClass F t) (rawClass F s)] with ω hs ht hu hd
  rw [hs, hd, Pi.sub_apply, ht, hu]
  simp only [step, constant, increment, Pi.mul_apply, Pi.sub_apply, one_mul]

theorem unit_sumClass (F : JointL2) (τ : ℕ → ℝ≥0) (n : ℕ) :
    sumClass F τ (fun i => constant (τ i) 1) n = rawClass F (τ n) - rawClass F (τ 0) := by
  apply Lp.ext
  filter_upwards [sumClass_ae F τ (fun i => constant (τ i) 1) n,
    rawClass_ae F (τ n), rawClass_ae F (τ 0),
    Lp.coeFn_sub (rawClass F (τ n)) (rawClass F (τ 0))] with ω hs ht hu hd
  rw [hs, hd, Pi.sub_apply, ht, hu]
  exact congrFun (unit_sum F τ n) ω

theorem unit_energy_bound (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) :
    ‖stepClass F s t (constant s 1)‖ ^ 2 ≤ ‖F‖ ^ 2 := by
  have hm : rawClass F s ∈ past s := Submodule.starProjection_apply_mem _ _
  have ho := past_inner_step_zero F hst (constant s 1) _ hm
  have he : rawClass F t = rawClass F s + stepClass F s t (constant s 1) := by
    rw [unit_stepClass]; abel
  have hn := pow_le_pow_left₀ (norm_nonneg _) ((past t).norm_starProjection_apply_le F) 2
  change ‖rawClass F t‖ ^ 2 ≤ ‖F‖ ^ 2 at hn
  rw [he, norm_add_sq_real, ho] at hn
  nlinarith [sq_nonneg ‖rawClass F s‖]

theorem step_norm_bound (F : JointL2) (s t : ℝ≥0) (a : Coefficient s) (C : ℝ)
    (hC : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖a.function ω‖ ≤ C) :
    ‖stepClass F s t a‖ ≤ C * ‖stepClass F s t (constant s 1)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [stepClass_ae F s t a, stepClass_ae F s t (constant s 1), hC] with ω ha hu hc
  rw [ha, hu]
  simp only [step, constant, Pi.mul_apply, one_mul]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

theorem grid_energy_bound (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖(a i).function ω‖ ≤ C) (n : ℕ) :
    ‖sumClass F τ a n‖ ^ 2 ≤ C ^ 2 * ‖F‖ ^ 2 := by
  calc
    _ = ∑ i ∈ Finset.range n, ‖stepClass F (τ i) (τ (i + 1)) (a i)‖ ^ 2 :=
      energy_identity F τ hτ a n
    _ ≤ ∑ i ∈ Finset.range n, C ^ 2 * ‖stepClass F (τ i) (τ (i + 1)) (constant (τ i) 1)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hb := step_norm_bound F (τ i) (τ (i + 1)) (a i) C (ha i)
      simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hC (norm_nonneg _))).mpr hb
    _ = C ^ 2 * ‖sumClass F τ (fun i => constant (τ i) 1) n‖ ^ 2 := by
      rw [energy_identity F τ hτ, Finset.mul_sum]
    _ = C ^ 2 * ‖stepClass F (τ 0) (τ n) (constant (τ 0) 1)‖ ^ 2 := by
      rw [unit_sumClass, unit_stepClass]
    _ ≤ _ := mul_le_mul_of_nonneg_left (unit_energy_bound F (hτ (Nat.zero_le n))) (sq_nonneg C)

theorem bounded_energy_summable (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖(a i).function ω‖ ≤ C) :
    Summable (fun i => ‖stepClass F (τ i) (τ (i + 1)) (a i)‖ ^ 2) := by
  apply summable_of_sum_range_le (fun i => sq_nonneg _) (c := C ^ 2 * ‖F‖ ^ 2)
  intro n
  rw [← energy_identity F τ hτ a n]
  exact grid_energy_bound F τ hτ a C hC ha n

end OperatorDerivativeRewrite.Foundation.IBMTerminalIntegralEnergy
