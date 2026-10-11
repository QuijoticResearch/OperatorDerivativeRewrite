import Foundation.PoissonBoundedCalculus

/-! Bounded multipliers of the maximal one-site Poisson difference, with L²-valued product rules. -/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonMultipliers
open OperatorDerivativeRewrite.Foundation
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonWeightedDomains PoissonCoordinateEvaluation PoissonBoundedCalculus

private theorem bounded_memLp_infty {μ : Measure ℕ} [IsFiniteMeasure μ] (g : ℕ → ℝ) (C : ℝ)
    (hg : ∀ n, |g n| ≤ C) : MemLp g ∞ μ := by
  apply MemLp.of_bound (by fun_prop) C
  filter_upwards [] with n
  simpa only [Real.norm_eq_abs] using hg n

private theorem weighted_field_finite (rate : ℝ≥0) :
    IsFiniteMeasure ((rate : ℝ≥0∞) • poissonLaw rate) := ⟨by
  change (rate : ℝ≥0∞) * (poissonLaw rate) Set.univ < ∞
  simp⟩

theorem scalar_mul_memLp (rate : ℝ≥0) (f : ScalarL2 rate) (g : ℕ → ℝ)
    (C : ℝ) (hg : ∀ n, |g n| ≤ C) :
    MemLp (fun n => g n * f n) 2 (poissonLaw rate) :=
  mul_Linfty_L2_memLp_two (bounded_memLp_infty g C hg) (Lp.memLp f)

def scalarMul (rate : ℝ≥0) (f : ScalarL2 rate) (g : ℕ → ℝ)
    (C : ℝ) (hg : ∀ n, |g n| ≤ C) : ScalarL2 rate :=
  (scalar_mul_memLp rate f g C hg).toLp (fun n => g n * f n)

theorem scalarMul_apply (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) (n : ℕ) :
    (scalarMul rate f g C hg) n = g n * f n :=
  ae_eq_implies_pointwise rate hr (MemLp.coeFn_toLp (scalar_mul_memLp rate f g C hg)) n

theorem scalarMul_eq_of_bounds (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate)
    (g : ℕ → ℝ) (C C' : ℝ) (hg : ∀ n, |g n| ≤ C) (hg' : ∀ n, |g n| ≤ C') :
    scalarMul rate f g C hg = scalarMul rate f g C' hg' := by
  apply Lp.ext
  filter_upwards [] with n
  rw [scalarMul_apply rate hr, scalarMul_apply rate hr]


theorem field_mul_memLp (rate : ℝ≥0) (u : FieldL2 rate) (g : ℕ → ℝ)
    (C : ℝ) (hg : ∀ n, |g n| ≤ C) :
    MemLp (fun n => g n * u n) 2 ((rate : ℝ≥0∞) • poissonLaw rate) := by
  have := weighted_field_finite rate
  exact mul_Linfty_L2_memLp_two (bounded_memLp_infty g C hg) (Lp.memLp u)

def fieldMul (rate : ℝ≥0) (u : FieldL2 rate) (g : ℕ → ℝ)
    (C : ℝ) (hg : ∀ n, |g n| ≤ C) : FieldL2 rate :=
  (field_mul_memLp rate u g C hg).toLp (fun n => g n * u n)

theorem fieldMul_apply (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) (n : ℕ) :
    (fieldMul rate u g C hg) n = g n * u n :=
  weighted_ae_eq_implies_pointwise rate hr
    (MemLp.coeFn_toLp (field_mul_memLp rate u g C hg)) n

theorem fieldMul_eq_of_bounds (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate)
    (g : ℕ → ℝ) (C C' : ℝ) (hg : ∀ n, |g n| ≤ C) (hg' : ∀ n, |g n| ≤ C') :
    fieldMul rate u g C hg = fieldMul rate u g C' hg' := by
  apply Lp.ext
  filter_upwards [] with n
  rw [fieldMul_apply rate hr, fieldMul_apply rate hr]

def scalarAsField (rate : ℝ≥0) (f : ScalarL2 rate) : FieldL2 rate :=
  (scalar_memLp_weighted rate f).toLp (fun n => f n)

theorem scalarAsField_apply (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (n : ℕ) : (scalarAsField rate f) n = f n :=
  weighted_ae_eq_implies_pointwise rate hr
    (MemLp.coeFn_toLp (scalar_memLp_weighted rate f)) n

theorem bounded_difference_bound (g : ℕ → ℝ) (C : ℝ)
    (hg : ∀ n, |g n| ≤ C) (n : ℕ) : |g (n + 1) - g n| ≤ 2 * C := by
  calc
    _ ≤ |g (n + 1)| + |g n| := abs_sub _ _
    _ ≤ C + C := add_le_add (hg (n + 1)) (hg n)
    _ = _ := by ring

/-- This is the actual maximal derivative of the bounded multiplier. -/
def boundedDifference (rate : ℝ≥0) (hr : 0 < rate) (g : ℕ → ℝ)
    (C : ℝ) (hg : ∀ n, |g n| ≤ C) : FieldL2 rate :=
  (maximalDifference rate hr) ⟨scalarOfBounded rate g C hg,
    bounded_scalar_mem_maximalDifference rate hr g C hg⟩

theorem boundedDifference_apply (rate : ℝ≥0) (hr : 0 < rate) (g : ℕ → ℝ)
    (C : ℝ) (hg : ∀ n, |g n| ≤ C) (n : ℕ) :
    (boundedDifference rate hr g C hg) n = g (n + 1) - g n :=
  bounded_difference_apply rate hr g C hg n

theorem boundedDifference_bound (rate : ℝ≥0) (hr : 0 < rate) (g : ℕ → ℝ)
    (C : ℝ) (hg : ∀ n, |g n| ≤ C) (n : ℕ) :
    |(boundedDifference rate hr g C hg) n| ≤ 2 * C := by
  rw [boundedDifference_apply rate hr]
  exact bounded_difference_bound g C hg n

theorem shifted_memLp (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain) :
    MemLp (fun n => f (n + 1)) 2 ((rate : ℝ≥0∞) • poissonLaw rate) :=
  (shift_memLp_iff_difference_memLp rate f).mpr
    ((mem_maximalDifference_domain_iff_memLp_difference rate hr f).mp hf)

theorem shifted_multiplier_term_memLp (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) :
    MemLp (fun n => (boundedDifference rate hr g C hg) n * f (n + 1)) 2
      ((rate : ℝ≥0∞) • poissonLaw rate) := by
  have := weighted_field_finite rate
  exact mul_Linfty_L2_memLp_two
    (bounded_memLp_infty _ (2 * C) (boundedDifference_bound rate hr g C hg))
    (shifted_memLp rate hr f hf)

/-- The shifted term has the expected weighted L² norm bound. -/
theorem shifted_multiplier_term_norm_le (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) :
    ‖(shifted_multiplier_term_memLp rate hr f hf g C hg).toLp
      (fun n => (boundedDifference rate hr g C hg) n * f (n + 1))‖ ≤
      (2 * C) * ‖(shifted_memLp rate hr f hf).toLp (fun n => f (n + 1))‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards
    [MemLp.coeFn_toLp (shifted_multiplier_term_memLp rate hr f hf g C hg),
      MemLp.coeFn_toLp (shifted_memLp rate hr f hf)] with n hprod hshift
  rw [hprod, hshift, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right
    (boundedDifference_bound rate hr g C hg n) (abs_nonneg _)
theorem product_difference_memLp (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) :
    MemLp (fun n => (scalarMul rate f g C hg) (n + 1) -
      (scalarMul rate f g C hg) n) 2 ((rate : ℝ≥0∞) • poissonLaw rate) := by
  have hfirst := field_mul_memLp rate
    ((maximalDifference rate hr) ⟨f, hf⟩) g C hg
  have hsecond := shifted_multiplier_term_memLp rate hr f hf g C hg
  have hsum := hfirst.add hsecond
  convert hsum using 1
  funext n
  have hd := (maximalDifference rate hr).mem_graph ⟨f, hf⟩
  rw [maximalDifference_graph] at hd
  simp only [Pi.add_apply]
  rw [scalarMul_apply rate hr, scalarMul_apply rate hr, boundedDifference_apply rate hr]
  have hdf : ((maximalDifference rate hr) ⟨f, hf⟩) n = f (n + 1) - f n := hd n
  rw [hdf]
  ring

theorem scalarMul_mem_domain (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) :
    scalarMul rate f g C hg ∈ (maximalDifference rate hr).domain :=
  (mem_maximalDifference_domain_iff_memLp_difference rate hr _).mpr
    (product_difference_memLp rate hr f hf g C hg)

/-- The two-term shifted product rule as an equality in the actual weighted field L². -/
theorem scalarMul_difference_shifted (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) :
    (maximalDifference rate hr) ⟨scalarMul rate f g C hg,
      scalarMul_mem_domain rate hr f hf g C hg⟩ =
      fieldMul rate ((maximalDifference rate hr) ⟨f, hf⟩) g C hg +
      (shifted_multiplier_term_memLp rate hr f hf g C hg).toLp
        (fun n => (boundedDifference rate hr g C hg) n * f (n + 1)) := by
  apply Lp.ext
  filter_upwards [] with n
  have hd := (maximalDifference rate hr).mem_graph
    ⟨scalarMul rate f g C hg, scalarMul_mem_domain rate hr f hf g C hg⟩
  rw [maximalDifference_graph] at hd
  rw [field_add_apply rate hr, hd n,
    scalarMul_apply rate hr, scalarMul_apply rate hr,
    fieldMul_apply rate hr]
  rw [weighted_ae_eq_implies_pointwise rate hr
    (MemLp.coeFn_toLp (shifted_multiplier_term_memLp rate hr f hf g C hg)) n]
  have hdf := (maximalDifference rate hr).mem_graph ⟨f, hf⟩
  rw [maximalDifference_graph] at hdf
  rw [hdf n, boundedDifference_apply rate hr]
  ring

/-- The complete jump product rule, with each term a genuine weighted L² class. -/
theorem scalarMul_difference_expanded (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (hf : f ∈ (maximalDifference rate hr).domain)
    (g : ℕ → ℝ) (C : ℝ) (hg : ∀ n, |g n| ≤ C) :
    (maximalDifference rate hr) ⟨scalarMul rate f g C hg,
      scalarMul_mem_domain rate hr f hf g C hg⟩ =
      fieldMul rate (scalarAsField rate f)
        (fun n => (boundedDifference rate hr g C hg) n) (2 * C)
        (boundedDifference_bound rate hr g C hg) +
      fieldMul rate ((maximalDifference rate hr) ⟨f, hf⟩) g C hg +
      fieldMul rate ((maximalDifference rate hr) ⟨f, hf⟩)
        (fun n => (boundedDifference rate hr g C hg) n) (2 * C)
        (boundedDifference_bound rate hr g C hg) := by
  apply Lp.ext
  filter_upwards [] with n
  have hd := (maximalDifference rate hr).mem_graph
    ⟨scalarMul rate f g C hg, scalarMul_mem_domain rate hr f hf g C hg⟩
  rw [maximalDifference_graph] at hd
  rw [field_add_apply rate hr, field_add_apply rate hr, hd n,
    scalarMul_apply rate hr, scalarMul_apply rate hr,
    fieldMul_apply rate hr, fieldMul_apply rate hr, fieldMul_apply rate hr,
    scalarAsField_apply rate hr]
  have hdf := (maximalDifference rate hr).mem_graph ⟨f, hf⟩
  rw [maximalDifference_graph] at hdf
  rw [hdf n, boundedDifference_apply rate hr]
  ring


/-- Quantitative L² control by the multiplier's uniform bound. -/
theorem scalarMul_norm_le (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (g : ℕ → ℝ) (C : ℝ)
    (hg : ∀ n, |g n| ≤ C) : ‖scalarMul rate f g C hg‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [] with n
  rw [scalarMul_apply rate hr, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hg n) (abs_nonneg _)

/-- The same L² estimate in the rate-weighted field space. -/
theorem fieldMul_norm_le (rate : ℝ≥0) (hr : 0 < rate)
    (u : FieldL2 rate) (g : ℕ → ℝ) (C : ℝ)
    (hg : ∀ n, |g n| ≤ C) : ‖fieldMul rate u g C hg‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [] with n
  rw [fieldMul_apply rate hr, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hg n) (abs_nonneg _)

/-- A bounded Poisson L² class determines its representative at every atom. -/
theorem bounded_representatives_eq (rate : ℝ≥0) (hr : 0 < rate)
    (g g' : ℕ → ℝ) (C C' : ℝ)
    (hg : ∀ n, |g n| ≤ C) (hg' : ∀ n, |g' n| ≤ C')
    (heq : scalarOfBounded rate g C hg = scalarOfBounded rate g' C' hg')
    (n : ℕ) : g n = g' n := by
  have h := congrArg (fun v : ScalarL2 rate => v n) heq
  simpa only [scalarOfBounded_apply rate hr] using h

theorem scalarMul_eq_of_representatives (rate : ℝ≥0) (hr : 0 < rate)
    (f : ScalarL2 rate) (g g' : ℕ → ℝ) (C C' : ℝ)
    (hg : ∀ n, |g n| ≤ C) (hg' : ∀ n, |g' n| ≤ C')
    (heq : scalarOfBounded rate g C hg = scalarOfBounded rate g' C' hg') :
    scalarMul rate f g C hg = scalarMul rate f g' C' hg' := by
  apply Lp.ext
  filter_upwards [] with n
  rw [scalarMul_apply rate hr, scalarMul_apply rate hr,
    bounded_representatives_eq rate hr g g' C C' hg hg' heq n]

theorem fieldMul_eq_of_representatives (rate : ℝ≥0) (hr : 0 < rate)
    (u : FieldL2 rate) (g g' : ℕ → ℝ) (C C' : ℝ)
    (hg : ∀ n, |g n| ≤ C) (hg' : ∀ n, |g' n| ≤ C')
    (heq : scalarOfBounded rate g C hg = scalarOfBounded rate g' C' hg') :
    fieldMul rate u g C hg = fieldMul rate u g' C' hg' := by
  apply Lp.ext
  filter_upwards [] with n
  rw [fieldMul_apply rate hr, fieldMul_apply rate hr,
    bounded_representatives_eq rate hr g g' C C' hg hg' heq n]

theorem boundedDifference_eq_of_representatives (rate : ℝ≥0) (hr : 0 < rate)
    (g g' : ℕ → ℝ) (C C' : ℝ)
    (hg : ∀ n, |g n| ≤ C) (hg' : ∀ n, |g' n| ≤ C')
    (heq : scalarOfBounded rate g C hg = scalarOfBounded rate g' C' hg') :
    boundedDifference rate hr g C hg = boundedDifference rate hr g' C' hg' := by
  apply Lp.ext
  filter_upwards [] with n
  rw [boundedDifference_apply rate hr, boundedDifference_apply rate hr,
    bounded_representatives_eq rate hr g g' C C' hg hg' heq (n + 1),
    bounded_representatives_eq rate hr g g' C C' hg hg' heq n]
end OperatorDerivativeRewrite.Foundation.PoissonMultipliers
