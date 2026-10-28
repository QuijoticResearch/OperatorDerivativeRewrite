import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! The block heat-reference factor in a Yang--Mills manuscript degenerates as coupling grows. -/

open Filter
open scoped Topology

noncomputable section
namespace OperatorDerivativeRewrite.Foundation.YMBlockRateDegeneration

def referenceFactor (A ell β : ℝ) : ℝ := Real.exp (-(ell / (A * β)))

theorem referenceFactor_pos (A ell β : ℝ) : 0 < referenceFactor A ell β := by
  unfold referenceFactor
  positivity

theorem referenceFactor_lt_one (A ell β : ℝ)
    (hA : 0 < A) (hell : 0 < ell) (hβ : 0 < β) :
    referenceFactor A ell β < 1 := by
  unfold referenceFactor
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr (div_pos hell (mul_pos hA hβ)))

theorem referenceFactor_tendsto_one (A ell : ℝ) (hA : A ≠ 0) :
    Tendsto (referenceFactor A ell) atTop (𝓝 1) := by
  have ht : Tendsto (fun β : ℝ => (-ell / A) * β⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.const_mul (-ell / A))
  have he : Tendsto (fun β : ℝ => Real.exp ((-ell / A) * β⁻¹)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp ht
  apply he.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
  unfold referenceFactor
  congr 1
  field_simp

theorem no_uniform_reference_contraction (A ell : ℝ)
    (hA : 0 < A) (_hell : 0 < ell) :
    ¬ ∃ q : ℝ, q < 1 ∧ ∀ β : ℝ, 0 < β → referenceFactor A ell β ≤ q := by
  rintro ⟨q, hq, hbound⟩
  have hev : ∀ᶠ β : ℝ in atTop, referenceFactor A ell β ≤ q := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact hbound β hβ
  have hlim : (1 : ℝ) ≤ q := le_of_tendsto (referenceFactor_tendsto_one A ell hA.ne') hev
  linarith

theorem no_uniform_total_contraction (A ell : ℝ)
    (hA : 0 < A) (hell : 0 < ell)
    (error₁ error₂ : ℝ → ℝ)
    (h₁ : ∀ β : ℝ, 0 < β → 0 ≤ error₁ β)
    (h₂ : ∀ β : ℝ, 0 < β → 0 ≤ error₂ β) :
    ¬ ∃ q : ℝ, q < 1 ∧ ∀ β : ℝ, 0 < β →
      referenceFactor A ell β + error₁ β + error₂ β ≤ q := by
  intro h
  apply no_uniform_reference_contraction A ell hA hell
  obtain ⟨q, hq, hb⟩ := h
  refine ⟨q, hq, ?_⟩
  intro β hβ
  have hh := hb β hβ
  linarith [h₁ β hβ, h₂ β hβ]

theorem referenceFactor_nat_power (A ell : ℝ) (hA : A ≠ 0) (n : ℕ) (hn : 0 < n) :
    referenceFactor A ell (n : ℝ) ^ n = Real.exp (-(ell / A)) := by
  rw [referenceFactor, ← Real.exp_nat_mul]
  congr 1
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp


theorem referenceFactor_macro_steps (A ell : ℝ) (hA : A ≠ 0)
    (n k : ℕ) (hn : 0 < n) :
    referenceFactor A ell (n : ℝ) ^ (n * k) =
      Real.exp ((-(ell / A)) * (k : ℝ)) := by
  rw [pow_mul, referenceFactor_nat_power A ell hA n hn, ← Real.exp_nat_mul]
  congr 1
  ring

theorem referenceFactor_varying_macro_decay (A ell : ℝ)
    (hA : 0 < A) (hell : 0 < ell)
    (n : ℕ → ℕ) (hn : ∀ k, 0 < n k) :
    Tendsto (fun k : ℕ =>
      referenceFactor A ell ((n k : ℕ) : ℝ) ^ (n k * k)) atTop (𝓝 0) := by
  have hq0 : 0 ≤ Real.exp (-(ell / A)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(ell / A)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr (div_pos hell hA))
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have he : (fun k : ℕ =>
      referenceFactor A ell ((n k : ℕ) : ℝ) ^ (n k * k)) =
      (fun k : ℕ => Real.exp (-(ell / A)) ^ k) := by
    funext k
    rw [referenceFactor_macro_steps A ell hA.ne' (n k) k (hn k),
      mul_comm (-(ell / A)) (k : ℝ), Real.exp_nat_mul]
  rw [he]
  exact hp

end OperatorDerivativeRewrite.Foundation.YMBlockRateDegeneration
