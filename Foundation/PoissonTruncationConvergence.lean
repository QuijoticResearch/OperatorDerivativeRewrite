import Foundation.PoissonTruncation
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Foundation.PoissonWeightedDomains

/-! Ambient L² convergence of finite-coordinate restrictions on countable finite measure spaces. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonTruncationConvergence
open PoissonTruncation PoissonDifferenceCore PoissonDifferenceOperators
open PoissonMaximalOperators PoissonWeightedDomains

/-- Restriction of any L² function on ℕ to its first `N` coordinates. -/
def cut (g : ℕ → ℝ) (N : ℕ) (n : ℕ) : ℝ := if n < N then g n else 0

variable {μ : Measure ℕ} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem cut_memLp (g : ℕ → ℝ) (hg : MemLp g 2 μ) (N : ℕ) :
    MemLp (cut g N) 2 μ := by
  apply hg.of_le (by fun_prop)
  filter_upwards [] with n
  by_cases hn : n < N <;> simp [cut, hn]

/-- The same finite-coordinate restrictions converge in genuine `Lp`, not merely pointwise. -/
theorem cut_toLp_tendsto (g : ℕ → ℝ) (hg : MemLp g 2 μ) :
    Tendsto (fun N => (cut_memLp g hg N).toLp (cut g N)) atTop
      (𝓝 (hg.toLp g)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (cut g)
    (cut_memLp g hg) g hg).2
  have hconst : UnifIntegrable (fun _ : ℕ => g) 2 μ :=
    unifIntegrable_const (by norm_num) (by simp) hg
  have hui : UnifIntegrable (cut g) 2 μ := by
    apply hconst.ae_mono (fun _ => by fun_prop)
    intro N
    filter_upwards [] with n
    by_cases hn : n < N <;> simp [cut, hn]
  have hpt (n : ℕ) : Tendsto (fun N => cut g N n) atTop (𝓝 (g n)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    simp [cut, show n < N by omega]
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by simp)
    (fun _ => by fun_prop) hg hui (Filter.Eventually.of_forall hpt)

/-- Scalar finite-coordinate Poisson classes converge in their actual Hilbert norm. -/
theorem scalar_truncate_tendsto (rate : ℝ≥0) (f : ScalarL2 rate) :
    Tendsto (fun N => scalarFinsupp rate (truncate (fun n => f n) N))
      atTop (𝓝 f) := by
  have h := cut_toLp_tendsto (μ := poissonLaw rate) (fun n => f n) (Lp.memLp f)
  rw [Lp.toLp_coeFn] at h
  convert h using 1
  ext N
  filter_upwards [scalarFinsupp_coeFn rate (truncate (fun n => f n) N),
    MemLp.coeFn_toLp (cut_memLp (fun n => f n) (Lp.memLp f) N)] with n hn hc
  rw [hn, hc]
  rfl

/-- Field finite-coordinate Poisson classes converge in the rate-weighted Hilbert norm. -/
theorem field_truncate_tendsto (rate : ℝ≥0) (u : FieldL2 rate) :
    Tendsto (fun N => fieldFinsupp rate (truncate (fun n => u n) N))
      atTop (𝓝 u) := by
  have : IsFiniteMeasure ((rate : ℝ≥0∞) • poissonLaw rate) := ⟨by
    change (rate : ℝ≥0∞) * (poissonLaw rate) Set.univ < ∞
    simp⟩
  have h := cut_toLp_tendsto
    (μ := (rate : ℝ≥0∞) • poissonLaw rate) (fun n => u n) (Lp.memLp u)
  rw [Lp.toLp_coeFn] at h
  convert h using 1
  ext N
  filter_upwards [fieldFinsupp_coeFn rate (truncate (fun n => u n) N),
    MemLp.coeFn_toLp (cut_memLp (fun n => u n) (Lp.memLp u) N)] with n hn hc
  rw [hn, hc]
  rfl

/-- A truncated difference is the cutoff of the full difference plus one outgoing boundary atom. -/
theorem difference_truncate_decomposition (f : ℕ → ℝ) (N : ℕ) :
    finsuppDifference (truncate f (N + 1)) =
      truncate (fun n => f (n + 1) - f n) N + Finsupp.single N (-f N) := by
  ext n
  simp only [finsuppDifference_apply, Finsupp.add_apply, truncate_apply]
  by_cases hlt : n < N
  · have h0 : n < N + 1 := by omega
    have h1 : n + 1 < N + 1 := by omega
    have hne : N ≠ n := by omega
    simp [h0, h1, hlt, hne]
  by_cases heq : n = N
  · subst n
    have h0 : N < N + 1 := by omega
    simp [h0]
  · have h0 : ¬ n < N + 1 := by omega
    have h1 : ¬ n + 1 < N + 1 := by omega
    have hne : N ≠ n := by omega
    simp [h0, h1, hlt, hne]
end OperatorDerivativeRewrite.Foundation.PoissonTruncationConvergence
