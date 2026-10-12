import Foundation.PoissonMultipliers

/-! Algebraic composition and commutators for actual bounded multipliers of the
maximal one-site Poisson difference. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.PoissonMultiplierAlgebra
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonCoordinateEvaluation
open PoissonMultipliers

/-- Uniformly bounded count functions are closed under addition. -/
theorem bounded_add (g k : ℕ → ℝ) (C B : ℝ)
    (hg : ∀ n, |g n| ≤ C) (hk : ∀ n, |k n| ≤ B) (n : ℕ) :
    |g n + k n| ≤ C + B :=
  (abs_add_le _ _).trans (add_le_add (hg n) (hk n))

/-- Uniformly bounded count functions are closed under multiplication. -/
theorem bounded_mul (g k : ℕ → ℝ) (C B : ℝ)
    (hg : ∀ n, |g n| ≤ C) (hk : ∀ n, |k n| ≤ B) (n : ℕ) :
    |g n * k n| ≤ C * B :=
  PoissonBoundedCalculus.bounded_mul g k C B hg hk n

/-- Multiplication by bounded count functions composes on scalar Poisson L². -/
theorem scalarMul_comp (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate)
    (g k : ℕ → ℝ) (C B : ℝ)
    (hg : ∀ n, |g n| ≤ C) (hk : ∀ n, |k n| ≤ B) :
    scalarMul rate (scalarMul rate f g C hg) k B hk =
      scalarMul rate f (fun n => g n * k n) (C * B)
        (bounded_mul g k C B hg hk) := by
  apply Lp.ext
  filter_upwards [] with n
  rw [scalarMul_apply rate hr, scalarMul_apply rate hr,
    scalarMul_apply rate hr]
  ring

/-- Bounded count multipliers preserve the exact maximal difference domain. -/
theorem product_mem_domain (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (g k : ℕ → ℝ) (C B : ℝ)
    (hg : ∀ n, |g n| ≤ C) (hk : ∀ n, |k n| ≤ B) :
    scalarMul rate (scalarMul rate f g C hg) k B hk ∈
      (maximalDifference rate hr).domain :=
  scalarMul_mem_domain rate hr _ (scalarMul_mem_domain rate hr f hf g C hg) k B hk

/-- The commutator is the shifted multiplier term in the actual weighted field L². -/
theorem difference_commutator (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) :
    (maximalDifference rate hr)
      ⟨scalarMul rate f g C hg, scalarMul_mem_domain rate hr f hf g C hg⟩ -
      fieldMul rate ((maximalDifference rate hr) ⟨f, hf⟩) g C hg =
      (shifted_multiplier_term_memLp rate hr f hf g C hg).toLp
        (fun n => (boundedDifference rate hr g C hg) n * f (n + 1)) := by
  rw [scalarMul_difference_shifted]
  exact add_sub_cancel_left _ _

/-- The graph-output estimate retains the shift norm, which cannot generally
be replaced by the ambient scalar norm without a further weighted estimate. -/
theorem difference_product_norm_le (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) :
    ‖(maximalDifference rate hr)
      ⟨scalarMul rate f g C hg, scalarMul_mem_domain rate hr f hf g C hg⟩‖ ≤
      C * ‖(maximalDifference rate hr) ⟨f, hf⟩‖ +
      (2 * C) * ‖(shifted_memLp rate hr f hf).toLp
        (fun n => f (n + 1))‖ := by
  conv_lhs => rw [scalarMul_difference_shifted rate hr f hf g C hg]
  exact (norm_add_le _ _).trans
    (add_le_add (fieldMul_norm_le rate hr _ g C hg)
      (shifted_multiplier_term_norm_le rate hr f hf g C hg))

/-- Multiplication by bounded count functions respects addition on scalar L². -/
theorem scalarMul_add (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate)
    (g k : ℕ → ℝ) (C B : ℝ)
    (hg : ∀ n, |g n| ≤ C) (hk : ∀ n, |k n| ≤ B) :
    scalarMul rate f (fun n => g n + k n) (C + B)
      (bounded_add g k C B hg hk) =
      scalarMul rate f g C hg + scalarMul rate f k B hk := by
  apply Lp.ext
  filter_upwards [] with n
  rw [scalarMul_apply rate hr, scalar_add_apply rate hr,
    scalarMul_apply rate hr, scalarMul_apply rate hr]
  ring

/-- The alternate shifted product rule, with the multiplier shifted instead of the input. -/
theorem difference_product_shifted_multiplier (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) :
    (maximalDifference rate hr)
      ⟨scalarMul rate f g C hg, scalarMul_mem_domain rate hr f hf g C hg⟩ =
      fieldMul rate (scalarAsField rate f)
        (fun n => (boundedDifference rate hr g C hg) n) (2 * C)
        (boundedDifference_bound rate hr g C hg) +
      fieldMul rate ((maximalDifference rate hr) ⟨f, hf⟩)
        (fun n => g (n + 1)) C (fun n => hg (n + 1)) := by
  apply Lp.ext
  filter_upwards [] with n
  have hd := (maximalDifference rate hr).mem_graph
    ⟨scalarMul rate f g C hg, scalarMul_mem_domain rate hr f hf g C hg⟩
  rw [maximalDifference_graph] at hd
  rw [field_add_apply rate hr, hd n,
    scalarMul_apply rate hr, scalarMul_apply rate hr,
    fieldMul_apply rate hr, fieldMul_apply rate hr,
    scalarAsField_apply rate hr, boundedDifference_apply rate hr]
  have hdf := (maximalDifference rate hr).mem_graph ⟨f, hf⟩
  rw [maximalDifference_graph] at hdf
  rw [hdf n]
  ring
end OperatorDerivativeRewrite.Foundation.PoissonMultiplierAlgebra





