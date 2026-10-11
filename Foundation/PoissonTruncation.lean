import Foundation.PoissonWeightedDomains

/-! Finite-coordinate Poisson truncations and their exact graph boundary terms. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.PoissonTruncation
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonWeightedDomains

/-- Coordinate cutoff strictly below `N`, as an actual finite-support function. -/
def truncate (f : ℕ → ℝ) (N : ℕ) : ℕ →₀ ℝ :=
  Finsupp.ofSupportFinite (fun n => if n < N then f n else 0) (by
    apply Set.Finite.subset (Finset.range N).finite_toSet
    intro n hn
    by_contra hnot
    have hnN : ¬ n < N := by simpa using hnot
    simp only [Function.mem_support] at hn
    simp [hnN] at hn)

@[simp] theorem truncate_apply (f : ℕ → ℝ) (N n : ℕ) :
    truncate f N n = if n < N then f n else 0 := rfl

/-- The difference agrees with the original formula strictly inside the cutoff. -/
theorem difference_truncate_interior (f : ℕ → ℝ) (N n : ℕ) (hn : n < N) :
    forwardDifference (truncate f (N + 1)) n = f (n + 1) - f n := by
  have h1 : n + 1 < N + 1 := by omega
  have h0 : n < N + 1 := by omega
  simp [forwardDifference, truncate_apply, h1, h0]

/-- The difference has one outgoing boundary term at the last retained count. -/
theorem difference_truncate_boundary (f : ℕ → ℝ) (N : ℕ) :
    forwardDifference (truncate f (N + 1)) N = -f N := by
  have h0 : N < N + 1 := by omega
  have h1 : ¬ N + 1 < N + 1 := by omega
  simp [forwardDifference, truncate_apply, h0]

/-- The difference vanishes beyond the truncation boundary. -/
theorem difference_truncate_tail (f : ℕ → ℝ) (N n : ℕ) (hn : N < n) :
    forwardDifference (truncate f (N + 1)) n = 0 := by
  have h0 : ¬ n < N + 1 := by omega
  have h1 : ¬ n + 1 < N + 1 := by omega
  simp [forwardDifference, truncate_apply, h0, h1]

/-- The divergence agrees with the original formula at every retained count. -/
theorem divergence_truncate_interior (rate : ℝ≥0) (u : ℕ → ℝ)
    (N n : ℕ) (hn : n ≤ N) :
    poissonDivergenceExpr rate (truncate u (N + 1)) n =
      maximalDivergenceExpr rate u n := by
  cases n with
  | zero =>
      have h0 : 0 < N + 1 := by omega
      simp [divergence_at_zero, maximalDivergenceExpr, truncate_apply, h0]
  | succ n =>
      have h0 : n < N + 1 := by omega
      have h1 : n + 1 < N + 1 := by omega
      simp [divergence_at_succ, maximalDivergenceExpr, truncate_apply, h0, h1]

/-- The divergence has one incoming boundary term just after the cutoff. -/
theorem divergence_truncate_boundary (rate : ℝ≥0) (u : ℕ → ℝ) (N : ℕ) :
    poissonDivergenceExpr rate (truncate u (N + 1)) (N + 1) =
      (N + 1 : ℝ) * u N := by
  have h0 : N < N + 1 := by omega
  have h1 : ¬ N + 1 < N + 1 := by omega
  simp [divergence_at_succ, truncate_apply, h0]

/-- The divergence vanishes beyond its single incoming boundary count. -/
theorem divergence_truncate_tail (rate : ℝ≥0) (u : ℕ → ℝ)
    (N n : ℕ) (hn : N + 1 < n) :
    poissonDivergenceExpr rate (truncate u (N + 1)) n = 0 := by
  cases n with
  | zero => omega
  | succ n =>
      have h0 : ¬ n < N + 1 := by omega
      have h1 : ¬ n + 1 < N + 1 := by omega
      simp [divergence_at_succ, truncate_apply, h0, h1]

/-- The scalar cutoff boundary has vanishing Poisson L² mass. -/
theorem scalar_boundary_sq_tendsto_zero (rate : ℝ≥0) (f : ScalarL2 rate) :
    Filter.Tendsto (fun N => poissonWeight rate N * (f N)^2)
      Filter.atTop (nhds 0) :=
  ((memLp_two_iff_summable_weighted_sq rate (fun n => f n)).mp (Lp.memLp f)).tendsto_atTop_zero

/-- The incoming divergence boundary also vanishes under the exact maximal-domain moment. -/
theorem divergence_boundary_sq_tendsto_zero (rate : ℝ≥0) (hr : 0 < rate)
    (u : FieldL2 rate)
    (hu : u ∈ (maximalDivergence rate hr).domain) :
    Filter.Tendsto
      (fun N => poissonWeight rate (N + 1) * ((N + 1 : ℝ) * u N)^2)
      Filter.atTop (nhds 0) := by
  have hm := (mem_maximalDivergence_domain_iff_moment rate hr u).mp hu
  have hb : Summable (fun n => poissonWeight rate n *
      (backwardExpr (fun k => u k) n)^2) :=
    (summable_backward_sq_iff_moment rate hr _).mpr hm
  have hs : Summable (fun n => poissonWeight rate (n + 1) *
      (backwardExpr (fun k => u k) (n + 1))^2) :=
    (summable_nat_add_iff (f := fun n => poissonWeight rate n *
      (backwardExpr (fun k => u k) n)^2) 1).mpr hb
  simpa only [backwardExpr] using hs.tendsto_atTop_zero

end OperatorDerivativeRewrite.Foundation.PoissonTruncation
