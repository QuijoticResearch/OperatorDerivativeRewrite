import Foundation.BrownianSignIntegral

/-! Conditional consistency and exact covariance of the actual sign integral.
These are L2 statements, not a Brownian-law or continuous-version assertion. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianSignConditional
open InfiniteGaussian GaussianTimeProductL2 GaussianPredictableFull
open GaussianPredictableCutoff GaussianConditionalIto BrownianSignIntegral

theorem cut_field (S T : ℝ≥0) :
    predictableCut S (predictableField T) = predictableField (min S T) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [cut_coeFn S (field T), field_coeFn T, field_coeFn (min S T)]
    with z hc ht hm
  change cut S (field T) z = field (min S T) z
  rw [hc, hm]
  by_cases hS : z ∈ PredictableRealL2.horizon S
  · rw [indicator_of_mem hS, ht]
    by_cases hs : z.1 ≤ (S : ℝ) <;> by_cases ht : z.1 ≤ (T : ℝ) <;>
      by_cases hz : 0 < z.1 <;>
      simp_all [PredictableRealL2.horizon, NNReal.coe_min]
  · rw [indicator_of_notMem hS]
    by_cases hs : z.1 ≤ (S : ℝ) <;> by_cases ht : z.1 ≤ (T : ℝ) <;>
      by_cases hz : 0 < z.1 <;>
      simp_all [PredictableRealL2.horizon, NNReal.coe_min]

theorem conditional_projection (S T : ℝ≥0) :
    pastProjection S (terminal T) = terminal (min S T) := by
  rw [terminal, pastProjection_integral, cut_field]
  rfl

theorem terminal_past (T : ℝ≥0) : terminal T ∈ pastL2 T := by
  have h := integral_cut_mem_past T (predictableField T)
  rw [cut_field, min_self] at h
  exact h

theorem conditional_expectation (S T : ℝ≥0) (hST : S ≤ T) :
    gaussianProduct[terminal T | GaussianTimeProcess.naturalFiltration S]
      =ᵐ[gaussianProduct] terminal S := by
  have h := pastProjection_ae S (terminal T)
  rw [conditional_projection, min_eq_left hST] at h
  exact h.symm

theorem field_inner (S T : ℝ≥0) : inner ℝ (field S) (field T) = (min S T : ℝ≥0) := by
  rw [L2_inner_eq_integral, ← field_norm_sq (min S T),
    ← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [field_coeFn S, field_coeFn T, field_coeFn (min S T)] with z hs ht hm
  simp only [Real.inner_apply, hs, ht, hm]
  by_cases hs : z.1 ≤ (S : ℝ) <;> by_cases ht : z.1 ≤ (T : ℝ) <;>
    by_cases hz : 0 < z.1 <;>
    simp_all [PredictableRealL2.horizon, NNReal.coe_min]

theorem terminal_inner (S T : ℝ≥0) :
    inner ℝ (terminal S) (terminal T) = (min S T : ℝ≥0) := by
  unfold terminal
  rw [itoIntegral.inner_map_map]
  exact field_inner S T

theorem terminal_increment_norm_sq (S T : ℝ≥0) (hST : S ≤ T) :
    ‖terminal T - terminal S‖ ^ 2 = (T : ℝ) - S := by
  rw [norm_sub_sq_real, terminal_norm_sq, terminal_norm_sq, terminal_inner,
    min_eq_right hST]
  ring

end OperatorDerivativeRewrite.Foundation.BrownianSignConditional
