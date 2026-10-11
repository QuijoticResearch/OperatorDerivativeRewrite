import Foundation.PoissonAdjoints

/-! Bounded Poisson count functions form a multiplication domain for the closed difference. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonBoundedCalculus
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonWeightedDomains PoissonCoordinateEvaluation

/-- A pointwise bounded count function belongs to actual scalar Poisson L². -/
theorem bounded_scalar_memLp (rate : ℝ≥0) (g : ℕ → ℝ) (C : ℝ)
    (hg : ∀ n, |g n| ≤ C) : MemLp g 2 (poissonLaw rate) := by
  apply MemLp.of_bound (by fun_prop) C
  filter_upwards [] with n
  simpa only [Real.norm_eq_abs] using hg n

/-- A bounded count function also belongs to the rate-weighted field Hilbert space. -/
theorem bounded_field_memLp (rate : ℝ≥0) (g : ℕ → ℝ) (C : ℝ)
    (hg : ∀ n, |g n| ≤ C) :
    MemLp g 2 ((rate : ℝ≥0∞) • poissonLaw rate) := by
  have : IsFiniteMeasure ((rate : ℝ≥0∞) • poissonLaw rate) := ⟨by
    change (rate : ℝ≥0∞) * (poissonLaw rate) Set.univ < ∞
    simp⟩
  apply MemLp.of_bound (by fun_prop) C
  filter_upwards [] with n
  simpa only [Real.norm_eq_abs] using hg n

/-- The actual scalar L² class represented by a bounded count function. -/
def scalarOfBounded (rate : ℝ≥0) (g : ℕ → ℝ) (C : ℝ)
    (hg : ∀ n, |g n| ≤ C) : ScalarL2 rate :=
  (bounded_scalar_memLp rate g C hg).toLp g

/-- The actual weighted field L² class represented by a bounded count function. -/
def fieldOfBounded (rate : ℝ≥0) (g : ℕ → ℝ) (C : ℝ)
    (hg : ∀ n, |g n| ≤ C) : FieldL2 rate :=
  (bounded_field_memLp rate g C hg).toLp g

theorem scalarOfBounded_apply (rate : ℝ≥0) (hr : 0 < rate)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) (n : ℕ) :
    (scalarOfBounded rate g C hg) n = g n :=
  ae_eq_implies_pointwise rate hr (MemLp.coeFn_toLp (bounded_scalar_memLp rate g C hg)) n

theorem fieldOfBounded_apply (rate : ℝ≥0) (hr : 0 < rate)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) (n : ℕ) :
    (fieldOfBounded rate g C hg) n = g n :=
  weighted_ae_eq_implies_pointwise rate hr
    (MemLp.coeFn_toLp (bounded_field_memLp rate g C hg)) n

/-- The bound remains valid for the product of two bounded count functions. -/
theorem bounded_mul (f g : ℕ → ℝ) (Cf Cg : ℝ)
    (hf : ∀ n, |f n| ≤ Cf) (hg : ∀ n, |g n| ≤ Cg) (n : ℕ) :
    |f n * g n| ≤ Cf * Cg := by
  rw [abs_mul]
  exact mul_le_mul (hf n) (hg n) (abs_nonneg _) (by linarith [hf n, abs_nonneg (f n)])

/-- The actual bounded product belongs to the maximal difference domain. -/
theorem bounded_product_mem_maximalDifference (rate : ℝ≥0) (hr : 0 < rate)
    (f g : ℕ → ℝ) (Cf Cg : ℝ)
    (hf : ∀ n, |f n| ≤ Cf) (hg : ∀ n, |g n| ≤ Cg) :
    scalarOfBounded rate (fun n => f n * g n) (Cf * Cg) (bounded_mul f g Cf Cg hf hg) ∈
      (maximalDifference rate hr).domain := by
  rw [mem_maximalDifference_domain_iff_memLp_difference rate hr]
  have hbound (n : ℕ) :
      |(f (n + 1) * g (n + 1)) - f n * g n| ≤ 2 * (Cf * Cg) := by
    calc
      _ ≤ |f (n + 1) * g (n + 1)| + |f n * g n| := abs_sub _ _
      _ ≤ Cf * Cg + Cf * Cg := add_le_add (bounded_mul f g Cf Cg hf hg (n + 1))
        (bounded_mul f g Cf Cg hf hg n)
      _ = _ := by ring
  have hm := bounded_field_memLp rate
    (fun n => f (n + 1) * g (n + 1) - f n * g n) (2 * (Cf * Cg)) hbound
  convert hm using 1
  funext n
  rw [scalarOfBounded_apply rate hr, scalarOfBounded_apply rate hr]


/-- Every bounded scalar count function lies in the maximal difference domain. -/
theorem bounded_scalar_mem_maximalDifference (rate : ℝ≥0) (hr : 0 < rate)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) :
    scalarOfBounded rate g C hg ∈ (maximalDifference rate hr).domain := by
  rw [mem_maximalDifference_domain_iff_memLp_difference rate hr]
  have hbound (n : ℕ) : |g (n + 1) - g n| ≤ 2 * C := by
    calc
      _ ≤ |g (n + 1)| + |g n| := abs_sub _ _
      _ ≤ C + C := add_le_add (hg (n + 1)) (hg n)
      _ = _ := by ring
  have hm := bounded_field_memLp rate (fun n => g (n + 1) - g n) (2 * C) hbound
  convert hm using 1
  funext n
  rw [scalarOfBounded_apply rate hr, scalarOfBounded_apply rate hr]

/-- The closed difference acts by the actual finite difference on bounded representatives. -/
theorem bounded_difference_apply (rate : ℝ≥0) (hr : 0 < rate)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) (n : ℕ) :
    ((maximalDifference rate hr) ⟨scalarOfBounded rate g C hg,
      bounded_scalar_mem_maximalDifference rate hr g C hg⟩) n =
      g (n + 1) - g n := by
  have hh := (maximalDifference rate hr).mem_graph
    ⟨scalarOfBounded rate g C hg,
      bounded_scalar_mem_maximalDifference rate hr g C hg⟩
  rw [maximalDifference_graph] at hh
  simpa only [scalarOfBounded_apply rate hr] using hh n

/-- The genuine maximal difference obeys the non-Gaussian product rule on bounded functions. -/
theorem bounded_difference_product_rule (rate : ℝ≥0) (hr : 0 < rate)
    (f g : ℕ → ℝ) (Cf Cg : ℝ)
    (hf : ∀ n, |f n| ≤ Cf) (hg : ∀ n, |g n| ≤ Cg) (n : ℕ) :
    ((maximalDifference rate hr) ⟨scalarOfBounded rate (fun k => f k * g k)
      (Cf * Cg) (bounded_mul f g Cf Cg hf hg),
      bounded_product_mem_maximalDifference rate hr f g Cf Cg hf hg⟩) n =
      f n * ((maximalDifference rate hr) ⟨scalarOfBounded rate g Cg hg,
        bounded_scalar_mem_maximalDifference rate hr g Cg hg⟩) n +
      g n * ((maximalDifference rate hr) ⟨scalarOfBounded rate f Cf hf,
        bounded_scalar_mem_maximalDifference rate hr f Cf hf⟩) n +
      ((maximalDifference rate hr) ⟨scalarOfBounded rate f Cf hf,
        bounded_scalar_mem_maximalDifference rate hr f Cf hf⟩) n *
      ((maximalDifference rate hr) ⟨scalarOfBounded rate g Cg hg,
        bounded_scalar_mem_maximalDifference rate hr g Cg hg⟩) n := by
  rw [bounded_difference_apply rate hr (fun k => f k * g k)
      (Cf * Cg) (bounded_mul f g Cf Cg hf hg) n,
    bounded_difference_apply rate hr g Cg hg n,
    bounded_difference_apply rate hr f Cf hf n]
  ring
end OperatorDerivativeRewrite.Foundation.PoissonBoundedCalculus
