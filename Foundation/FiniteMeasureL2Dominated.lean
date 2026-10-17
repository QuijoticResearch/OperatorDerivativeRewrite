import Foundation.BochnerL2Dominated

/-! Dominated convergence for actual L2 classes under a uniform finite-measure bound. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteMeasureL2Dominated
set_option backward.isDefEq.respectTransparency false
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

theorem tendsto_of_constant_bound (f : ℕ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C)
    (hg : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds (g x))) :
    Tendsto f atTop (nhds g) := by
  have hi := tendsto_integral_of_dominated_convergence (fun _ : α => 4*C^2)
    (F := fun n x => ‖f n x - g x‖^2) (f := fun _ => (0 : ℝ))
    (fun n => ((Lp.aestronglyMeasurable (f n)).sub (Lp.aestronglyMeasurable g)).norm.pow 2)
    (integrable_const _) (fun n => ?_) ?_
  · have he (n : ℕ) : ‖f n - g‖^2 = ∫ x, ‖f n x - g x‖^2 ∂μ := by
      rw [BochnerL2Dominated.norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (f n) g] with x hx
      simp only [hx, Pi.sub_apply]
    simp only [integral_zero] at hi
    have hn : Tendsto (fun n => ‖f n - g‖^2) atTop (nhds 0) := by
      simpa only [he] using hi
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hs
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hs
  · filter_upwards [hf n, hg] with x hfx hgx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hn := norm_sub_le (f n x) (g x)
    nlinarith [norm_nonneg (f n x - g x)]
  · filter_upwards [ht] with x hx
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((hx.sub (tendsto_const_nhds (x := g x))).norm.pow 2)

theorem toLp_tendsto_of_constant_bound (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (C : ℝ) (hC : 0 ≤ C) (hfb : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C)
    (hgb : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (nhds (hg.toLp g)) := by
  apply tendsto_of_constant_bound _ _ C hC
  · intro n
    filter_upwards [MemLp.coeFn_toLp (hf n), hfb n] with x hx hbx
    rw [hx]
    exact hbx
  · filter_upwards [MemLp.coeFn_toLp hg, hgb] with x hx hbx
    rw [hx]
    exact hbx
  · have hr : ∀ᵐ x ∂μ, ∀ n, (hf n).toLp (f n) x = f n x :=
      ae_all_iff.mpr (fun n => MemLp.coeFn_toLp (hf n))
    filter_upwards [hr, MemLp.coeFn_toLp hg, ht] with x hx hgx htx
    simpa only [hx, hgx] using htx

end OperatorDerivativeRewrite.Foundation.FiniteMeasureL2Dominated
