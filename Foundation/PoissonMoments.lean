import Foundation.PoissonBoundedCalculus

/-! Genuine polynomial moment summability for a positive-rate Poisson law. -/
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonMoments
open PoissonDifferenceCore PoissonDifferenceOperators

/-- Every natural-power moment of the actual Poisson weights is summable. -/
theorem summable_poisson_power_moment (rate : ℝ≥0) (hr : 0 < rate) (k : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * poissonWeight rate n) := by
  let a : ℕ → ℝ := fun n => (n : ℝ) ^ k * poissonWeight rate n
  have hrR : (0 : ℝ) < rate := by exact_mod_cast hr
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (rate : ℝ) * 2 ^ k)
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop (max 1 N)] with n hn
  have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
  have hnN : N ≤ n := (le_max_right 1 N).trans hn
  have hlarge : 2 * (rate : ℝ) * 2 ^ k ≤ (n + 1 : ℝ) := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hnN
    linarith
  have hpow : ((n + 1 : ℝ) ^ k) ≤ 2 ^ k * (n : ℝ) ^ k := by
    have hnn : (n + 1 : ℝ) ≤ 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
    calc
      _ ≤ (2 * (n : ℝ)) ^ k := pow_le_pow_left₀ (by positivity) hnn k
      _ = _ := by ring
  have hwn : 0 ≤ poissonWeight rate n := (poisson_weight_pos rate hr n).le
  have hws : 0 ≤ poissonWeight rate (n + 1) :=
    (poisson_weight_pos rate hr (n + 1)).le
  have hweight := poisson_weight_succ rate n
  have ht := mul_le_mul_of_nonneg_right hlarge hws
  rw [hweight] at ht
  have hRate : (rate : ℝ) * (2 * 2 ^ k * poissonWeight rate (n + 1)) ≤
      (rate : ℝ) * poissonWeight rate n := by nlinarith [ht]
  have hfactor : 2 ^ k * poissonWeight rate (n + 1) ≤
      (1 / 2 : ℝ) * poissonWeight rate n := by
    have hh := le_of_mul_le_mul_left hRate hrR
    linarith
  change ‖a (n + 1)‖ ≤ (1 / 2 : ℝ) * ‖a n‖
  have ha : 0 ≤ a n := mul_nonneg (by positivity) hwn
  have has : 0 ≤ a (n + 1) := mul_nonneg (by positivity) hws
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg has]
  have hcalc : (n + 1 : ℝ) ^ k * poissonWeight rate (n + 1) ≤
      (1 / 2 : ℝ) * ((n : ℝ) ^ k * poissonWeight rate n) := by
    calc
    _ ≤ (2 ^ k * (n : ℝ) ^ k) * poissonWeight rate (n + 1) :=
      mul_le_mul_of_nonneg_right hpow hws
    _ = (n : ℝ) ^ k * (2 ^ k * poissonWeight rate (n + 1)) := by ring
    _ ≤ (n : ℝ) ^ k * ((1 / 2 : ℝ) * poissonWeight rate n) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = _ := by ring
  simpa only [a, Nat.cast_add, Nat.cast_one] using hcalc


/-- Every count monomial defines a genuine scalar Poisson L² class. -/
theorem poisson_power_memLp_two (rate : ℝ≥0) (hr : 0 < rate) (k : ℕ) :
    MemLp (fun n : ℕ => (n : ℝ) ^ k) 2 (poissonLaw rate) := by
  rw [PoissonWeightedDomains.memLp_two_iff_summable_weighted_sq]
  convert summable_poisson_power_moment rate hr (2 * k) using 1
  ext n
  simp only [pow_mul]
  ring

/-- All ordinary polynomial count functions have finite second Poisson moment. -/
theorem polynomial_memLp_two (rate : ℝ≥0) (hr : 0 < rate)
    (p : Polynomial ℝ) : MemLp (fun n : ℕ => p.eval (n : ℝ)) 2 (poissonLaw rate) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      convert hp.add hq using 1
      funext n
      simp only [Polynomial.eval_add, Pi.add_apply]
  | monomial n a =>
      have hm := (poisson_power_memLp_two rate hr n).mul_const a
      convert hm using 1
      funext k
      simp [Polynomial.eval_monomial, mul_comm]

/-- The actual Poisson masses sum to one. -/
theorem tsum_poissonWeight (rate : ℝ≥0) :
    (∑' n, poissonWeight rate n) = 1 := by
  simpa only [poissonWeight, poissonLaw, poissonMeasure_real_singleton] using
    (ProbabilityTheory.hasSum_one_poissonMeasure rate).tsum_eq

/-- The first count moment has the exact Poisson normalization. -/
theorem tsum_poisson_count (rate : ℝ≥0) (hr : 0 < rate) :
    (∑' n : ℕ, (n : ℝ) * poissonWeight rate n) = rate := by
  have hs := (summable_poisson_power_moment rate hr 1).sum_add_tsum_nat_add 1
  simp only [pow_one, Finset.sum_range_one, Nat.cast_zero, zero_mul,
    zero_add, Nat.cast_add, Nat.cast_one] at hs
  have he : (∑' n : ℕ, (n + 1 : ℝ) * poissonWeight rate (n + 1)) =
      (rate : ℝ) * (∑' n, poissonWeight rate n) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    exact poisson_weight_succ rate n
  rw [he, tsum_poissonWeight] at hs
  simpa using hs.symm

/-- The second count moment is λ² + λ. -/
theorem tsum_poisson_count_sq (rate : ℝ≥0) (hr : 0 < rate) :
    (∑' n : ℕ, (n : ℝ)^2 * poissonWeight rate n) =
      (rate : ℝ)^2 + rate := by
  have hs := (summable_poisson_power_moment rate hr 2).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0),
    zero_mul, zero_add] at hs
  have he : (∑' n : ℕ, ((n + 1 : ℕ) : ℝ)^2 * poissonWeight rate (n + 1)) =
      (rate : ℝ) * (∑' n : ℕ, ((n : ℝ) + 1) * poissonWeight rate n) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have hw := poisson_weight_succ rate n
    push_cast
    nlinarith [hw]
  rw [he] at hs
  have hw : Summable (fun n : ℕ => poissonWeight rate n) :=
    (ProbabilityTheory.hasSum_one_poissonMeasure rate).summable.congr (by
      intro n
      simp [poissonWeight, poissonLaw, poissonMeasure_real_singleton])
  have hn := summable_poisson_power_moment rate hr 1
  have hadd : (∑' n : ℕ, ((n : ℝ) + 1) * poissonWeight rate n) =
      (∑' n : ℕ, (n : ℝ) * poissonWeight rate n) +
        (∑' n : ℕ, poissonWeight rate n) := by
    simp_rw [add_mul, one_mul]
    have hcount : Summable (fun n : ℕ => (n : ℝ) * poissonWeight rate n) := by
      simpa only [pow_one] using hn
    exact hcount.tsum_add hw
  rw [hadd, tsum_poisson_count rate hr, tsum_poissonWeight] at hs
  nlinarith [hs]

/-- The count has a genuine integrable expectation equal to the rate. -/
theorem integral_poisson_count (rate : ℝ≥0) (hr : 0 < rate) :
    (∫ n : ℕ, (n : ℝ) ∂poissonLaw rate) = rate := by
  have hp : MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonLaw rate) := by
    simpa only [pow_one] using poisson_power_memLp_two rate hr 1
  have hi : Integrable (fun n : ℕ => (n : ℝ)) (poissonLaw rate) :=
    hp.integrable (by norm_num)
  rw [integral_eq_weighted_tsum rate _ hi]
  calc
    _ = ∑' n : ℕ, (n : ℝ) * poissonWeight rate n := by
      apply tsum_congr
      intro n
      ring
    _ = _ := tsum_poisson_count rate hr

/-- The genuine second Poisson integral is λ² + λ. -/
theorem integral_poisson_count_sq (rate : ℝ≥0) (hr : 0 < rate) :
    (∫ n : ℕ, (n : ℝ)^2 ∂poissonLaw rate) = (rate : ℝ)^2 + rate := by
  have hi := (poisson_power_memLp_two rate hr 2).integrable (by norm_num)
  rw [integral_eq_weighted_tsum rate _ hi]
  calc
    _ = ∑' n : ℕ, (n : ℝ)^2 * poissonWeight rate n := by
      apply tsum_congr
      intro n
      ring
    _ = _ := tsum_poisson_count_sq rate hr
end OperatorDerivativeRewrite.Foundation.PoissonMoments
