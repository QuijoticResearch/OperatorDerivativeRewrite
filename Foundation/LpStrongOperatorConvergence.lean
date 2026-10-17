import Foundation.HigherHeatLpControls
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Strongly convergent contractions act strongly on actual Bochner L^(2m) fields. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.LpStrongOperatorConvergence
open HigherHeatLpControls

variable {α E F : Type*} [MeasurableSpace α] (μ : Measure α)
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem norm_integral (m : ℕ) [Fact (0 < m)] (f : Lp F (power m) μ) :
    ‖f‖ = (∫ s, ‖f s‖ ^ (2*m) ∂μ) ^ (((2*m : ℕ) : ℝ)⁻¹) := by
  have hn := lpNorm_eq_integral_norm_rpow_toReal (power_ne_zero m) (power_ne_top m)
    (Lp.aestronglyMeasurable f)
  rw [← toReal_eLpNorm, ← Lp.norm_def] at hn
  simpa only [power, ENNReal.toReal_natCast, Real.rpow_natCast] using hn

theorem compLp_tendsto (m : ℕ) [h : Fact (0 < m)] (L : ℕ → E →L[ℂ] F) (A : E →L[ℂ] F)
    (hL : ∀ n, ‖L n‖ ≤ 1) (hA : ‖A‖ ≤ 1)
    (hpoint : ∀ v, Tendsto (fun n => L n v) atTop (𝓝 (A v))) (f : Lp E (power m) μ) :
    Tendsto (fun n => (L n).compLpL (power m) μ f) atTop
      (𝓝 (A.compLpL (power m) μ f)) := by
  have hm := h.out
  have hp : 2*m ≠ 0 := by omega
  have hn (n : ℕ) (s : α) : ‖L n (f s) - A (f s)‖ ≤ 2*‖f s‖ := by
    calc
      _ ≤ ‖L n (f s)‖ + ‖A (f s)‖ := norm_sub_le _ _
      _ ≤ 1*‖f s‖ + 1*‖f s‖ := add_le_add
        ((L n).le_of_opNorm_le (hL n) _) (A.le_of_opNorm_le hA _)
      _ = _ := by ring
  have hb : Integrable (fun s => (2*‖f s‖)^(2*m)) μ := by
    have hi := (Lp.memLp f).integrable_norm_pow hp
    simpa only [mul_pow] using hi.const_mul ((2 : ℝ)^(2*m))
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun s => ‖L n (f s) - A (f s)‖ ^ (2*m)) μ :=
    (((L n).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).sub
      (A.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))).norm.pow _
  have hI : Tendsto (fun n => ∫ s, ‖L n (f s) - A (f s)‖^(2*m) ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ : α => (0 : ℝ))
      (fun s => (2*‖f s‖)^(2*m)) hmeas hb
      (fun n => Eventually.of_forall (fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hn n s) (2*m)))
      (Eventually.of_forall (fun s => by
        simpa only [sub_self, norm_zero, zero_pow hp] using ((hpoint (f s)).sub_const (A (f s))).norm.pow (2*m)))
    simpa only [integral_zero] using ht
  have he (n : ℕ) :
      ‖(L n).compLpL (power m) μ f - A.compLpL (power m) μ f‖ =
        (∫ s, ‖L n (f s) - A (f s)‖^(2*m) ∂μ) ^ (((2*m : ℕ) : ℝ)⁻¹) := by
    rw [norm_integral μ m]
    congr 1
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((L n).compLpL (power m) μ f) (A.compLpL (power m) μ f),
      (L n).coeFn_compLpL f, A.coeFn_compLpL f] with s hs h₁ h₂
    rw [hs]
    simp only [Pi.sub_apply, h₁, h₂]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (Real.continuous_rpow_const (show 0 ≤ (((2*m : ℕ) : ℝ)⁻¹) by positivity)).continuousAt.tendsto.comp hI
  have hz : (0 : ℝ) ^ (((2*m : ℕ) : ℝ)⁻¹) = 0 := Real.zero_rpow (by positivity)
  simpa only [Function.comp_def, he, hz] using ht

end OperatorDerivativeRewrite.Foundation.LpStrongOperatorConvergence
