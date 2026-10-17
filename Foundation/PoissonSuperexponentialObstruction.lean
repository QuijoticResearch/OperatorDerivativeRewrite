import Foundation.PoissonEntireMoments

/-! Quadratic exponential growth is outside the genuine Poisson integrability domain. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonSuperexponentialObstruction
open ComplexRootPoissonLaw

def term (r : ℝ≥0) (c : ℝ) (n : ℕ) : ℝ := weight r n * Real.exp (c*(n : ℝ)^2)

theorem term_nonneg (r : ℝ≥0) (c : ℝ) (n : ℕ) : 0 ≤ term r c n := by
  unfold term
  exact mul_nonneg (weight_nonneg r n) (Real.exp_nonneg _)

theorem term_pos (r : ℝ≥0) (hr : 0 < r) (c : ℝ) (n : ℕ) : 0 < term r c n := by
  unfold term weight
  positivity

theorem recurrence (r : ℝ≥0) (c : ℝ) (n : ℕ) :
    term r c (n+1)*((n : ℝ)+1) =
      (r : ℝ)*Real.exp (c*(2*(n : ℝ)+1))*term r c n := by
  have he : Real.exp (c*((n+1 : ℕ) : ℝ)^2) =
      Real.exp (c*(n : ℝ)^2)*Real.exp (c*(2*(n : ℝ)+1)) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  unfold term weight
  rw [he]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem step_growth (r : ℝ≥0) (_hr : 0 < r) (c : ℝ) (hc : 0 < c) (n : ℕ)
    (hn : 1 ≤ (n : ℝ)) (hA : 2 ≤ (r : ℝ) * c^2 * (n : ℝ)) :
    2*term r c n ≤ term r c (n+1) := by
  have hx : 0 ≤ c*(2*(n : ℝ)+1) := by positivity
  have he := Real.pow_div_factorial_le_exp (c*(2*(n : ℝ)+1)) hx 2
  norm_num at he
  have hp : 2*c^2*(n : ℝ)^2 ≤ Real.exp (c*(2*(n : ℝ)+1)) := by
    nlinarith [mul_nonneg (sq_nonneg c) (Nat.cast_nonneg n), sq_nonneg c]
  have hrate : 2*((n : ℝ)+1) ≤ (r : ℝ)*Real.exp (c*(2*(n : ℝ)+1)) := by
    calc
      _ ≤ 4*(n : ℝ) := by linarith
      _ ≤ 2*((r : ℝ)*c^2*(n : ℝ))*(n : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg n)]
      _ = (r : ℝ)*(2*c^2*(n : ℝ)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp r.coe_nonneg
  refine le_of_mul_le_mul_right ?_ (by positivity : 0 < (n : ℝ)+1)
  calc
    (2*term r c n)*((n : ℝ)+1) = term r c n*(2*((n : ℝ)+1)) := by ring
    _ ≤ term r c n*((r : ℝ)*Real.exp (c*(2*(n : ℝ)+1))) :=
      mul_le_mul_of_nonneg_left hrate (term_nonneg r c n)
    _ = term r c (n+1)*((n : ℝ)+1) := by rw [recurrence]; ring

theorem eventually_step_growth (r : ℝ≥0) (hr : 0 < r) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 2*term r c n ≤ term r c (n+1) := by
  have hA : 0 < (r : ℝ)*c^2 := by positivity
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hg := (hn.const_mul_atTop hA).eventually (eventually_ge_atTop 2)
  have h1 := hn.eventually (eventually_ge_atTop 1)
  filter_upwards [hg,h1] with n hn' hn1
  exact step_growth r hr c hc n hn1 hn'

theorem not_summable_subsequence (r : ℝ≥0) (hr : 0 < r) (c : ℝ) (hc : 0 < c)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop) :
    ¬ Summable (fun n => term r c (k n)) := by
  intro hs
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_step_growth r hr c hc)
  have hl : ∀ n, N ≤ n → term r c N ≤ term r c n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      have hq : term r c n ≤ 2*term r c n := by linarith [term_nonneg r c n]
      exact ih.trans (hq.trans (hN n hn))
  have hu := hs.tendsto_atTop_zero.eventually (Iio_mem_nhds (term_pos r hr c N))
  obtain ⟨n,hn,hn'⟩ := ((hk.eventually (eventually_ge_atTop N)).and hu).exists
  exact (not_lt_of_ge (hl (k n) hn)) hn'

theorem not_summable_terms (r : ℝ≥0) (hr : 0 < r) (c : ℝ) (hc : 0 < c) :
    ¬ Summable (term r c) :=
  not_summable_subsequence r hr c hc id tendsto_id

theorem not_integrable (r : ℝ≥0) (hr : 0 < r) (c : ℝ) (hc : 0 < c) :
    ¬ Integrable (fun n : ℕ => Real.exp (c*(n : ℝ)^2)) (poissonMeasure r) := by
  intro hi
  apply not_summable_terms r hr c hc
  change Summable (fun n => term r c n)
  simpa only [term, weight, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    integrable_poissonMeasure_iff.mp hi

end OperatorDerivativeRewrite.Foundation.PoissonSuperexponentialObstruction
