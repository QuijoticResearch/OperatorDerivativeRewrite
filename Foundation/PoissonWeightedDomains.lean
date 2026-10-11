import Foundation.PoissonMaximalOperators

/-! Weighted summability criteria for maximal one-site Poisson operator domains. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.PoissonWeightedDomains
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonCoordinateEvaluation

variable (rate : ℝ≥0) (hr : 0 < rate)

/-- For a discrete Poisson law, L² is exactly weighted square summability. -/
theorem memLp_two_iff_summable_weighted_sq (g : ℕ → ℝ) :
    MemLp g 2 (poissonLaw rate) ↔
      Summable (fun n => poissonWeight rate n * (g n)^2) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop), poissonLaw,
    integrable_poissonMeasure_iff]
  simp only [poissonWeight, poissonLaw, poissonMeasure_real_singleton,
    Real.norm_eq_abs, abs_sq]

/-- Positive rate makes the weighted field L² criterion the same square series. -/
theorem memLp_two_weighted_iff_summable_weighted_sq (hr : 0 < rate) (g : ℕ → ℝ) :
    MemLp g 2 ((rate : ℝ≥0∞) • poissonLaw rate) ↔
      Summable (fun n => poissonWeight rate n * (g n)^2) := by
  have hr0 : (rate : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  rw [memLp_two_iff_integrable_sq (by fun_prop),
    integrable_smul_measure hr0 (by finiteness),
    ← memLp_two_iff_integrable_sq (by fun_prop),
    memLp_two_iff_summable_weighted_sq]

/-- The Poisson recurrence reindexes square-summability of the forward shift
as the first weighted count moment, including the zero-count boundary. -/
theorem summable_shift_sq_iff_moment (hr : 0 < rate) (g : ℕ → ℝ) :
    Summable (fun n => poissonWeight rate n * (g (n + 1))^2) ↔
      Summable (fun n : ℕ => (n : ℝ) * poissonWeight rate n * (g n)^2) := by
  have hr0 : (rate : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hterm (n : ℕ) :
      (rate : ℝ) * (poissonWeight rate n * (g (n + 1))^2) =
        (n + 1 : ℝ) * poissonWeight rate (n + 1) * (g (n + 1))^2 := by
    calc
      _ = ((rate : ℝ) * poissonWeight rate n) * (g (n + 1))^2 := by ring
      _ = ((n + 1 : ℝ) * poissonWeight rate (n + 1)) * (g (n + 1))^2 := by
        rw [poisson_weight_succ rate n]
      _ = _ := by ring
  rw [← summable_mul_left_iff hr0]
  simp_rw [hterm]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff (f := fun n : ℕ =>
      (n : ℝ) * poissonWeight rate n * (g n)^2) 1)

/-- A scalar L² class is also L² under the finite rate-scaled measure. -/
theorem scalar_memLp_weighted (f : ScalarL2 rate) :
    MemLp (fun n => f n) 2 ((rate : ℝ≥0∞) • poissonLaw rate) :=
  (Lp.memLp f).smul_measure (by finiteness)

/-- Shift and finite difference have identical L² membership when the input is L². -/
theorem shift_memLp_iff_difference_memLp (f : ScalarL2 rate) :
    MemLp (fun n => f (n + 1)) 2 ((rate : ℝ≥0∞) • poissonLaw rate) ↔
      MemLp (fun n => f (n + 1) - f n) 2
        ((rate : ℝ≥0∞) • poissonLaw rate) := by
  have hf := scalar_memLp_weighted rate f
  constructor
  · intro hs
    exact hs.sub hf
  · intro hd
    have hs := hd.add hf
    convert hs using 1
    funext n
    dsimp
    ring

/-- Maximal difference domain membership is exactly L² membership of its actual formula. -/
theorem mem_maximalDifference_domain_iff_memLp_difference (hr : 0 < rate)
    (f : ScalarL2 rate) :
    f ∈ (maximalDifference rate hr).domain ↔
      MemLp (fun n => f (n + 1) - f n) 2
        ((rate : ℝ≥0∞) • poissonLaw rate) := by
  constructor
  · intro hf
    have hg := (maximalDifference rate hr).mem_graph ⟨f, hf⟩
    rw [maximalDifference_graph] at hg
    have he : (fun n => f (n + 1) - f n) =
        (fun n => ((maximalDifference rate hr) ⟨f, hf⟩) n) := by
      funext n
      exact (hg n).symm
    rw [he]
    exact Lp.memLp _
  · intro hf
    let v : FieldL2 rate := hf.toLp (fun n => f (n + 1) - f n)
    apply LinearPMap.mem_domain_of_mem_graph (y := v)
    rw [maximalDifference_graph]
    intro n
    exact weighted_ae_eq_implies_pointwise rate hr (MemLp.coeFn_toLp hf) n

/-- The maximal difference domain has precisely the first Poisson count moment. -/
theorem mem_maximalDifference_domain_iff_moment (hr : 0 < rate)
    (f : ScalarL2 rate) :
    f ∈ (maximalDifference rate hr).domain ↔
      Summable (fun n : ℕ => (n : ℝ) * poissonWeight rate n * (f n)^2) := by
  rw [mem_maximalDifference_domain_iff_memLp_difference rate hr,
    ← shift_memLp_iff_difference_memLp rate f,
    memLp_two_weighted_iff_summable_weighted_sq rate hr,
    summable_shift_sq_iff_moment rate hr]

/-- A weighted-field L² class is unweighted Poisson L² when the rate is positive. -/
theorem field_memLp_unweighted (hr : 0 < rate) (u : FieldL2 rate) :
    MemLp (fun n => u n) 2 (poissonLaw rate) := by
  have hr0 : (rate : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  exact (integrable_smul_measure hr0 (by finiteness)).mp
    ((memLp_two_iff_integrable_sq (by fun_prop)).1 (Lp.memLp u))

/-- The incoming Poisson shift, with zero at the count-zero boundary. -/
def backwardExpr (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (n + 1 : ℝ) * u n

/-- The backward shift square series is exactly the next-count weighted moment. -/
theorem summable_backward_sq_iff_moment (hr : 0 < rate) (u : ℕ → ℝ) :
    Summable (fun n => poissonWeight rate n * (backwardExpr u n)^2) ↔
      Summable (fun n : ℕ => (n + 1 : ℝ) * poissonWeight rate n * (u n)^2) := by
  have hr0 : (rate : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hterm (n : ℕ) :
      poissonWeight rate (n + 1) * (backwardExpr u (n + 1))^2 =
        (rate : ℝ) * ((n + 1 : ℝ) * poissonWeight rate n * (u n)^2) := by
    simp only [backwardExpr]
    have hw := poisson_weight_succ rate n
    linear_combination ((n + 1 : ℝ) * (u n)^2) * hw
  calc
    Summable (fun n => poissonWeight rate n * (backwardExpr u n)^2) ↔
        Summable (fun n => poissonWeight rate (n + 1) *
          (backwardExpr u (n + 1))^2) :=
      (summable_nat_add_iff (f := fun n =>
        poissonWeight rate n * (backwardExpr u n)^2) 1).symm
    _ ↔ Summable (fun n : ℕ => (rate : ℝ) *
        ((n + 1 : ℝ) * poissonWeight rate n * (u n)^2)) := by
      simp_rw [hterm]
    _ ↔ Summable (fun n : ℕ => (n + 1 : ℝ) * poissonWeight rate n * (u n)^2) :=
      summable_mul_left_iff hr0

/-- The incoming shift is L² exactly when the full divergence expression is L²;
the diagonal rate term is already L² for a field in the weighted Hilbert space. -/
theorem backward_memLp_iff_divergence_memLp (hr : 0 < rate)
    (u : FieldL2 rate) :
    MemLp (backwardExpr (fun n => u n)) 2 (poissonLaw rate) ↔
      MemLp (maximalDivergenceExpr rate (fun n => u n)) 2 (poissonLaw rate) := by
  have hu : MemLp (fun n => (rate : ℝ) * u n) 2 (poissonLaw rate) :=
    (field_memLp_unweighted rate hr u).const_mul _
  constructor
  · intro hb
    have hd := hb.sub hu
    convert hd using 1
    funext n
    cases n <;> simp [backwardExpr, maximalDivergenceExpr]
  · intro hd
    have hb := hd.add hu
    convert hb using 1
    funext n
    cases n <;> simp [backwardExpr, maximalDivergenceExpr]

/-- Maximal divergence domain membership is exactly L² membership of its actual formula. -/
theorem mem_maximalDivergence_domain_iff_memLp_divergence (hr : 0 < rate)
    (u : FieldL2 rate) :
    u ∈ (maximalDivergence rate hr).domain ↔
      MemLp (maximalDivergenceExpr rate (fun n => u n)) 2 (poissonLaw rate) := by
  constructor
  · intro hu
    have hg := (maximalDivergence rate hr).mem_graph ⟨u, hu⟩
    rw [maximalDivergence_graph] at hg
    have he : maximalDivergenceExpr rate (fun n => u n) =
        (fun n => ((maximalDivergence rate hr) ⟨u, hu⟩) n) := by
      funext n
      exact (hg n).symm
    rw [he]
    exact Lp.memLp _
  · intro hu
    let v : ScalarL2 rate := hu.toLp (maximalDivergenceExpr rate (fun n => u n))
    apply LinearPMap.mem_domain_of_mem_graph (y := v)
    rw [maximalDivergence_graph]
    intro n
    exact ae_eq_implies_pointwise rate hr (MemLp.coeFn_toLp hu) n

/-- The maximal divergence domain has precisely the next-count weighted moment. -/
theorem mem_maximalDivergence_domain_iff_moment (hr : 0 < rate)
    (u : FieldL2 rate) :
    u ∈ (maximalDivergence rate hr).domain ↔
      Summable (fun n : ℕ => (n + 1 : ℝ) * poissonWeight rate n * (u n)^2) := by
  rw [mem_maximalDivergence_domain_iff_memLp_divergence rate hr,
    ← backward_memLp_iff_divergence_memLp rate hr,
    memLp_two_iff_summable_weighted_sq rate,
    summable_backward_sq_iff_moment rate hr]

end OperatorDerivativeRewrite.Foundation.PoissonWeightedDomains
