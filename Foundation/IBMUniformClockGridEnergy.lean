import Foundation.IBMClockTraversalEnvelope
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform-grid summation of the genuine Brownian-clock traversal bound.
The singular diagonal retains its exact finite value. -/
noncomputable section
open MeasureTheory
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformClockGridEnergy
open IBMClockTraversalEnvelope IBMFoldedTransitionBound InfiniteGaussian

theorem inverse_sqrt_step (n : ℕ) :
    1 / Real.sqrt (n + 1 : ℝ) ≤
      2 * (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_iff₀ hp]
  nlinarith [Real.sq_sqrt hn, Real.sq_sqrt (by positivity : 0 ≤ (n + 1 : ℝ)),
    sq_nonneg (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ))]

/-- An elementary telescoping estimate, with no value at the singular zero
argument inserted in the sum. -/
theorem inverse_sqrt_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, 1 / Real.sqrt (i + 1 : ℝ)) ≤ 2 * Real.sqrt (n : ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        2 * (Real.sqrt (i + 1 : ℝ) - Real.sqrt (i : ℝ)) :=
      Finset.sum_le_sum fun i _ => inverse_sqrt_step i
    _ = _ := by
      rw [← Finset.mul_sum]
      have he := Finset.sum_range_sub (fun i : ℕ => Real.sqrt (i : ℝ)) n
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Real.sqrt_zero, sub_zero] at he
      rw [he]

def grid (h : ℝ≥0) (i : ℕ) : ℝ≥0 := h * i

theorem grid_injective {h : ℝ≥0} (hh : 0 < h) : Function.Injective (grid h) := by
  intro i j hij
  have he : (i : ℝ≥0) = j := mul_left_cancel₀ (ne_of_gt hh) hij
  exact_mod_cast he

theorem grid_peak (h : ℝ≥0) (i j : ℕ) (hij : i ≤ j) :
    peak (nndist ((grid h j : ℝ≥0) : ℝ) ((grid h i : ℝ≥0) : ℝ)) =
      peak h / Real.sqrt ((j - i : ℕ) : ℝ) := by
  have he : |((grid h j : ℝ≥0) : ℝ) - ((grid h i : ℝ≥0) : ℝ)| =
      (h : ℝ) * ((j - i : ℕ) : ℝ) := by
    have hijr : (i : ℝ) ≤ j := by exact_mod_cast hij
    simp only [grid, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_sub hij]
    rw [abs_of_nonneg (by nlinarith [h.coe_nonneg] : 0 ≤ (h : ℝ) * j - h * i)]
    ring
  simp only [peak, coe_nndist, Real.dist_eq, he]
  rw [show 2 * Real.pi * ((h : ℝ) * ((j - i : ℕ) : ℝ)) =
    (2 * Real.pi * h) * ((j - i : ℕ) : ℝ) by ring,
    Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi * h), mul_inv_rev]
  simp only [div_eq_mul_inv]
  ring

theorem pairBound_symm (δ : ℝ) (s t : ℝ≥0) : pairBound δ s t = pairBound δ t s := by
  by_cases h : s = t
  · subst t
    rfl
  · simp [pairBound, h, Ne.symm h, nndist_comm]

/-- The final row omits its diagonal and includes each positive distance once. -/
theorem last_row {h : ℝ≥0} (hh : 0 < h) (δ : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, pairBound δ (grid h n) (grid h j)) =
      (16 * δ ^ 2 * peak h) * ∑ j ∈ Finset.range n, 1 / Real.sqrt (j + 1 : ℝ) := by
  have he (j : ℕ) (hj : j < n) :
      pairBound δ (grid h n) (grid h j) =
        (16 * δ ^ 2 * peak h) * (1 / Real.sqrt ((n - j : ℕ) : ℝ)) := by
    have hne : grid h n ≠ grid h j := fun hc => (ne_of_gt hj) (grid_injective hh hc)
    rw [pairBound, ite_eq_right hne]
    rw [nndist_comm, grid_peak h j n hj.le]
    ring
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ j ∈ Finset.range n,
        (16 * δ ^ 2 * peak h) * (1 / Real.sqrt ((n - j : ℕ) : ℝ)) := by
      exact Finset.sum_congr rfl fun j hj => he j (Finset.mem_range.mp hj)
    _ = _ := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn := Finset.mem_range.mp hj
      have hn : n - (n - 1 - j) = j + 1 := by omega
      rw [hn]
      norm_cast

theorem last_row_le {h : ℝ≥0} (hh : 0 < h) (δ : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, pairBound δ (grid h n) (grid h j)) ≤
      32 * δ ^ 2 * peak h * Real.sqrt (n : ℝ) := by
  rw [last_row hh]
  exact (mul_le_mul_of_nonneg_left (inverse_sqrt_sum n)
    (mul_nonneg (by positivity) (peak_nonneg h))).trans_eq (by ring)

def sumBound (h : ℝ≥0) (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, pairBound δ (grid h i) (grid h j)

theorem sumBound_succ (h : ℝ≥0) (δ : ℝ) (n : ℕ) :
    sumBound h δ (n + 1) = sumBound h δ n + 2 * δ +
      2 * ∑ j ∈ Finset.range n, pairBound δ (grid h n) (grid h j) := by
  have hs : (∑ i ∈ Finset.range n, pairBound δ (grid h i) (grid h n)) =
      ∑ i ∈ Finset.range n, pairBound δ (grid h n) (grid h i) :=
    Finset.sum_congr rfl fun i _ => pairBound_symm δ _ _
  have hd : pairBound δ (grid h n) (grid h n) = 2 * δ := by simp [pairBound]
  simp only [sumBound, Finset.sum_range_succ, Finset.sum_add_distrib]
  rw [hs, hd]
  ring

/-- The diagonal contribution is linear in N; the inverse-square-root
off-diagonal sum grows at most N sqrt(N), rather than N squared. -/
theorem sumBound_le {h : ℝ≥0} (hh : 0 < h) (δ : ℝ) (n : ℕ) :
    sumBound h δ n ≤ 2 * δ * n + 64 * δ ^ 2 * peak h * n * Real.sqrt (n : ℝ) := by
  induction n with
  | zero => simp [sumBound]
  | succ n ih =>
    rw [sumBound_succ]
    have hr := last_row_le hh δ n
    have hs : Real.sqrt (n : ℝ) ≤ Real.sqrt (n + 1 : ℝ) :=
      Real.sqrt_le_sqrt (by linarith)
    have hc : 0 ≤ 64 * δ ^ 2 * peak h * (n + 1 : ℝ) := by
      exact mul_nonneg (mul_nonneg (by positivity) (peak_nonneg h)) (by positivity)
    have hm := mul_le_mul_of_nonneg_left hs hc
    push_cast
    nlinarith

/-- An expectation bound for the existing actual continuous Brownian clock on
a uniform grid. No maximum-increment event is silently removed. -/
theorem actual_uniform_energy_mean_le {h : ℝ≥0} (hh : 0 < h)
    {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    (∫ ω, energy (Finset.range n) (grid h) δ ω ∂gaussianProduct) ≤
      2 * δ * n + 64 * δ ^ 2 * peak h * n * Real.sqrt (n : ℝ) :=
  (energy_mean_le (Finset.range n) (grid h) hδ).trans (sumBound_le hh δ n)

theorem peak_div (T : ℝ≥0) (n : ℕ) :
    peak (T / n) = peak T * Real.sqrt (n : ℝ) := by
  unfold peak
  simp only [NNReal.coe_div, NNReal.coe_natCast]
  rw [← mul_div_assoc, Real.sqrt_div (by positivity), inv_div]
  ring

/-- Fixed positive horizon: the off-diagonal expectation grows at most N²,
with the horizon dependence isolated in the explicit factor peak(T). -/
theorem actual_horizon_energy_mean_le {T : ℝ≥0} (hT : 0 < T)
    {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) (hn : 0 < n) :
    (∫ ω, energy (Finset.range n) (grid (T / n)) δ ω ∂gaussianProduct) ≤
      2 * δ * n + 64 * δ ^ 2 * peak T * (n : ℝ) ^ 2 := by
  have hh : 0 < T / (n : ℝ≥0) := div_pos hT (by exact_mod_cast hn)
  have hb := actual_uniform_energy_mean_le hh hδ n
  rw [peak_div] at hb
  have he : 64 * δ ^ 2 * (peak T * Real.sqrt (n : ℝ)) * n * Real.sqrt (n : ℝ) =
      64 * δ ^ 2 * peak T * (n : ℝ) ^ 2 := by
    calc
      _ = 64 * δ ^ 2 * peak T * n * (Real.sqrt (n : ℝ)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]; ring
  rwa [he] at hb

theorem actual_weighted_energy_mean_le {T : ℝ≥0} (hT : 0 < T)
    {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) (hn : 0 < n) :
    (∫ ω, δ ^ 3 * energy (Finset.range n) (grid (T / n)) δ ω ∂gaussianProduct) ≤
      2 * n * δ ^ 4 + 64 * peak T * (n : ℝ) ^ 2 * δ ^ 5 := by
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (actual_horizon_energy_mean_le hT hδ n hn)
    (by positivity : 0 ≤ δ ^ 3)).trans_eq (by ring)

theorem rate_identity (x K : ℝ) (hx : 0 < x) :
    2 * x * (x ^ (-(4/9 : ℝ))) ^ 4 + K * x ^ 2 * (x ^ (-(4/9 : ℝ))) ^ 5 =
      2 * x ^ (-(7/9 : ℝ)) + K * x ^ (-(2/9 : ℝ)) := by
  have h4 : (x ^ (-(4/9 : ℝ))) ^ 4 = x ^ (-(16/9 : ℝ)) := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hx.le]
    norm_num
  have h5 : (x ^ (-(4/9 : ℝ))) ^ 5 = x ^ (-(20/9 : ℝ)) := by
    rw [← Real.rpow_natCast _ 5, ← Real.rpow_mul hx.le]
    norm_num
  have ha := Real.rpow_add hx 1 (-(16/9 : ℝ))
  have hb := Real.rpow_add hx 2 (-(20/9 : ℝ))
  norm_num only [Real.rpow_one, Real.rpow_two] at ha hb
  rw [h4, h5]
  calc
    _ = 2 * (x * x ^ (-(16/9 : ℝ))) + K * (x ^ 2 * x ^ (-(20/9 : ℝ))) := by ring
    _ = _ := by rw [← ha, ← hb]

/-- A verified decaying envelope for ALL uniform-grid sizes n+1, not merely
a sparse subsequence. Actual traversal domination still requires its bounded-
increment event; no joint quartic partition limit is asserted here. -/
theorem actual_weighted_energy_tendsto {T : ℝ≥0} (hT : 0 < T) :
    Filter.Tendsto (fun n : ℕ => ∫ ω,
      ((n + 1 : ℝ) ^ (-(4/9 : ℝ))) ^ 3 *
        energy (Finset.range (n + 1)) (grid (T / (n + 1)))
          ((n + 1 : ℝ) ^ (-(4/9 : ℝ))) ω ∂gaussianProduct)
      Filter.atTop (nhds 0) := by
  have hbound (n : ℕ) :
      (∫ ω, ((n + 1 : ℝ) ^ (-(4/9 : ℝ))) ^ 3 *
        energy (Finset.range (n + 1)) (grid (T / (n + 1)))
          ((n + 1 : ℝ) ^ (-(4/9 : ℝ))) ω ∂gaussianProduct) ≤
      2 * (n + 1 : ℝ) ^ (-(7/9 : ℝ)) +
        (64 * peak T) * (n + 1 : ℝ) ^ (-(2/9 : ℝ)) := by
    have hb := actual_weighted_energy_mean_le hT
      (δ := (n + 1 : ℝ) ^ (-(4/9 : ℝ)))
      (Real.rpow_nonneg (by positivity : 0 ≤ (n + 1 : ℝ)) _) (n + 1) (by omega)
    push_cast at hb
    simpa only [rate_identity _ _ (by positivity : 0 < (n + 1 : ℝ))] using hb
  have hn : Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h7 := (tendsto_rpow_neg_atTop (by norm_num : 0 < (7/9 : ℝ))).comp hn
  have h2 := (tendsto_rpow_neg_atTop (by norm_num : 0 < (2/9 : ℝ))).comp hn
  apply squeeze_zero (fun n => integral_nonneg fun ω => by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => tent_nonneg _ _) hbound
  simpa only [Function.comp_def, mul_zero, add_zero] using
    (h7.const_mul 2).add (h2.const_mul (64 * peak T))

end OperatorDerivativeRewrite.Foundation.IBMUniformClockGridEnergy
