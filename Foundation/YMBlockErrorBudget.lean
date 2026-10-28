import Foundation.YMBlockRateDegeneration
import Mathlib.Analysis.Real.Sqrt

/-! Exact error budget for the heat-reference block factor in a Yang--Mills manuscript. -/

open Filter
open scoped Topology
open OperatorDerivativeRewrite.Foundation.YMBlockRateDegeneration

namespace OperatorDerivativeRewrite.Foundation.YMBlockErrorBudget

theorem reference_deficit_le_inverse_coupling (A ell β : ℝ) :
    1 - referenceFactor A ell β ≤ ell / (A * β) := by
  have h := Real.add_one_le_exp (-(ell / (A * β)))
  unfold referenceFactor
  linarith

theorem strict_factor_requires_inverse_coupling_error (A ell β e₁ e₂ : ℝ)
    (hA : 0 < A) (hβ : 0 < β)
    (hq : referenceFactor A ell β + e₁ + e₂ < 1) :
    β * (e₁ + e₂) < ell / A := by
  have hdef := reference_deficit_le_inverse_coupling A ell β
  have he : e₁ + e₂ < ell / (A * β) := by linarith
  have hmul := (mul_lt_mul_of_pos_left he hβ)
  have hA0 : A ≠ 0 := hA.ne'
  have hβ0 : β ≠ 0 := hβ.ne'
  convert hmul using 1; field_simp


theorem fixed_sqrt_error_eventually_blocks_strictness (A ell c : ℝ)
    (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ β : ℝ in atTop,
      1 ≤ referenceFactor A ell β + c / Real.sqrt β := by
  have ht : Tendsto (fun β : ℝ => c * Real.sqrt β) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop hc
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    ht.eventually_gt_atTop (ell / A)] with β hβ hlarge
  by_contra hnot
  have hq : referenceFactor A ell β + c / Real.sqrt β < 1 := lt_of_not_ge hnot
  have he := strict_factor_requires_inverse_coupling_error
    A ell β 0 (c / Real.sqrt β) hA hβ (by simpa using hq)
  have hroot : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hid : β * (c / Real.sqrt β) = c * Real.sqrt β := by
    calc
      β * (c / Real.sqrt β) = (Real.sqrt β)^2 * (c / Real.sqrt β) := by
        rw [Real.sq_sqrt hβ.le]
      _ = c * Real.sqrt β := by field_simp
  rw [zero_add, hid] at he
  exact (not_lt_of_ge (le_of_lt he)) hlarge

theorem lower_sqrt_error_eventually_blocks_strictness (A ell c : ℝ)
    (hA : 0 < A) (hc : 0 < c)
    (error₁ error₂ : ℝ → ℝ)
    (hlower : ∀ᶠ β : ℝ in atTop,
      c / Real.sqrt β ≤ error₁ β + error₂ β) :
    ∀ᶠ β : ℝ in atTop,
      1 ≤ referenceFactor A ell β + error₁ β + error₂ β := by
  filter_upwards [fixed_sqrt_error_eventually_blocks_strictness A ell c hA hc,
    hlower] with β hreference herror
  linarith
end OperatorDerivativeRewrite.Foundation.YMBlockErrorBudget
