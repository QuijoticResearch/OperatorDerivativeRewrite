import Foundation.BrownianSmoothUniformCauchy
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! A concrete increasing subsequence with almost-sure eventually summable
compact-horizon increments, chosen from the proved uniform probability bounds. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianMassFastSubsequence
open InfiniteGaussian BrownianSmoothMassPath BrownianSmoothUniformCauchy

def tolerance (j : ℕ) : ℝ≥0 := (1 / 2) ^ j

theorem tolerance_pos (j : ℕ) : 0 < tolerance j := by unfold tolerance; positivity

def cutoff (j : ℕ) : ℕ := Classical.choose
  (mass_uniform_cauchy (j + 1) (tolerance j) (tolerance j)
    (tolerance_pos j) (tolerance_pos j))

theorem cutoff_spec (j : ℕ) : ∀ n ≥ cutoff j, ∀ m ≥ cutoff j,
    gaussianProduct {ω | ∃ t : ℝ≥0, t ≤ (j + 1 : ℝ≥0) ∧
      (tolerance j : ℝ) < ‖path n ω t - path m ω t‖} < (tolerance j : ℝ≥0∞) :=
  Classical.choose_spec (mass_uniform_cauchy (j + 1) (tolerance j) (tolerance j)
    (tolerance_pos j) (tolerance_pos j))

def subsequence : ℕ → ℕ
  | 0 => cutoff 0
  | j + 1 => max (subsequence j + 1) (cutoff (j + 1))

theorem subsequence_ge (j : ℕ) : cutoff j ≤ subsequence j := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact le_max_right _ _

theorem subsequence_strictMono : StrictMono subsequence := by
  apply strictMono_nat_of_lt_succ
  intro j
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

def bad (j : ℕ) : Set SampleSpace := {ω | ∃ t : ℝ≥0, t ≤ (j + 1 : ℝ≥0) ∧
  (tolerance j : ℝ) < ‖path (subsequence j) ω t - path (subsequence (j + 1)) ω t‖}

theorem bad_probability (j : ℕ) : gaussianProduct (bad j) < (tolerance j : ℝ≥0∞) :=
  cutoff_spec j (subsequence j) (subsequence_ge j) (subsequence (j + 1))
    ((subsequence_ge j).trans (subsequence_strictMono.monotone (Nat.le_succ j)))

theorem bad_summable : (∑' j, gaussianProduct (bad j)) ≠ ⊤ := by
  have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hf : (∑' j, (tolerance j : ℝ≥0∞)) ≠ ⊤ := by
    convert hs.tsum_ofReal_ne_top using 1
    congr 1
    funext j
    simp [tolerance, ENNReal.ofReal_pow]
  exact ne_top_of_le_ne_top hf (ENNReal.tsum_le_tsum (fun j => (bad_probability j).le))

theorem ae_eventual_increment : ∀ᵐ ω ∂gaussianProduct, ∀ᶠ j : ℕ in atTop,
    ∀ t : ℝ≥0, t ≤ (j + 1 : ℝ≥0) →
      ‖path (subsequence j) ω t - path (subsequence (j + 1)) ω t‖ ≤ (tolerance j : ℝ) := by
  filter_upwards [ae_eventually_notMem bad_summable] with ω hω
  filter_upwards [hω] with j hj t ht
  exact le_of_not_gt (fun he => hj ⟨t, ht, he⟩)

end OperatorDerivativeRewrite.Foundation.BrownianMassFastSubsequence
