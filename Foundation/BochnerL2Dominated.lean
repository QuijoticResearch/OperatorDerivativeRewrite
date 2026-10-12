import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space

/-! Dominated convergence for actual Hilbert-valued L2 classes. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BochnerL2Dominated
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {μ : Measure X}

theorem norm_sq_integral (f : Lp E 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem tendsto_of_ae_norm_bound (f : ℕ → Lp E 2 μ) (g : Lp E 2 μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖g x‖)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto f atTop (𝓝 g) := by
  have hi := tendsto_integral_of_dominated_convergence (fun x => 4 * ‖g x‖ ^ 2)
    (F := fun n x => ‖f n x - g x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun n => ((Lp.aestronglyMeasurable (f n)).sub (Lp.aestronglyMeasurable g)).norm.pow 2)
    (((Lp.memLp g).norm.integrable_sq).const_mul 4) (fun n => ?_) ?_
  · have he (n : ℕ) : ‖f n - g‖ ^ 2 = ∫ x, ‖f n x - g x‖ ^ 2 ∂μ := by
      rw [norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (f n) g] with x hx
      simp only [hx, Pi.sub_apply]
    simp only [integral_zero] at hi
    have hn : Tendsto (fun n => ‖f n - g‖ ^ 2) atTop (𝓝 0) := by simpa only [he] using hi
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hs
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hs
  · filter_upwards [hb n] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hn := norm_sub_le (f n x) (g x)
    nlinarith [norm_nonneg (f n x - g x), norm_nonneg (g x)]
  · filter_upwards [ht] with x hx
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((hx.sub (tendsto_const_nhds (x := g x))).norm.pow 2)

end OperatorDerivativeRewrite.Foundation.BochnerL2Dominated
