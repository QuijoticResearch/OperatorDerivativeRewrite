import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-! # Finite-support Poisson difference calculus

The measure is Mathlib's `ProbabilityTheory.poissonMeasure`. All integral
identities below include genuine integrability proofs for their integrands.
No closed operator or graph-domain identification is asserted in this module.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace OperatorDerivativeRewrite.Foundation.PoissonDifferenceCore

variable (rate : ℝ≥0)

/-- The actual Poisson law on natural-number counts. -/
abbrev poissonLaw : Measure ℕ := poissonMeasure rate

/-- The real mass of the singleton `{n}` under the Poisson law. -/
def poissonWeight (n : ℕ) : ℝ := (poissonLaw rate).real {n}

/-- The Poisson weights satisfy the exact successor recurrence. -/
theorem poisson_weight_succ (n : ℕ) :
    (n + 1 : ℝ) * poissonWeight rate (n + 1) =
      (rate : ℝ) * poissonWeight rate n := by
  simp only [poissonWeight, poissonLaw, poissonMeasure_real_singleton,
    Nat.factorial_succ, pow_succ]
  push_cast
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hns : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp


/-- At positive rate every count has strictly positive Poisson mass. -/
theorem poisson_weight_pos (hr : 0 < rate) (n : ℕ) :
    0 < poissonWeight rate n := by
  simpa only [poissonWeight, poissonLaw] using
    (poissonMeasure_real_singleton_pos n hr)
/-- The actual forward finite difference of a finite-support function. -/
def forwardDifference (f : ℕ →₀ ℝ) (n : ℕ) : ℝ := f (n + 1) - f n

/-- The Poisson backward coefficient, with its zero boundary at count zero. -/
def backwardWeighted (u : ℕ →₀ ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (n + 1 : ℝ) * u n

/-- The Poisson divergence expression on a finite-support vector. -/
def poissonDivergenceExpr (u : ℕ →₀ ℝ) (n : ℕ) : ℝ :=
  backwardWeighted u n - (rate : ℝ) * u n

/-- At count zero there is no incoming backward term. -/
theorem divergence_at_zero (u : ℕ →₀ ℝ) :
    poissonDivergenceExpr rate u 0 = -(rate : ℝ) * u 0 := by
  simp [poissonDivergenceExpr, backwardWeighted]

/-- At successor counts the backward coefficient has the count factor. -/
theorem divergence_at_succ (u : ℕ →₀ ℝ) (n : ℕ) :
    poissonDivergenceExpr rate u (n + 1) =
      (n + 1 : ℝ) * u n - (rate : ℝ) * u (n + 1) := by
  rfl
theorem shift_hasFiniteSupport (f : ℕ →₀ ℝ) :
    Function.HasFiniteSupport (fun n => f (n + 1)) := by
  exact f.hasFiniteSupport.comp_of_injective Nat.succ_injective

theorem difference_hasFiniteSupport (f : ℕ →₀ ℝ) :
    Function.HasFiniteSupport (forwardDifference f) := by
  exact (shift_hasFiniteSupport f).sub f.hasFiniteSupport

theorem backward_hasFiniteSupport (u : ℕ →₀ ℝ) :
    Function.HasFiniteSupport (backwardWeighted u) := by
  apply Set.Finite.subset (u.hasFiniteSupport.image Nat.succ)
  intro n hn
  cases n with
  | zero => simp [backwardWeighted] at hn
  | succ n =>
      simp only [Function.mem_support] at hn
      have hu : u n ≠ 0 := by
        intro hz
        simp [backwardWeighted, hz] at hn
      exact ⟨n, by simpa only [Function.mem_support] using hu, rfl⟩

theorem divergence_hasFiniteSupport (u : ℕ →₀ ℝ) :
    Function.HasFiniteSupport (poissonDivergenceExpr rate u) := by
  have hmul : Function.HasFiniteSupport (fun n => (rate : ℝ) * u n) := by
    apply Set.Finite.subset u.hasFiniteSupport
    intro n hn
    simp only [Function.mem_support] at hn ⊢
    exact (mul_ne_zero_iff.mp hn).2
  exact (backward_hasFiniteSupport u).sub hmul

/-- A real function with finite support is genuinely Poisson-integrable. -/
theorem integrable_of_finite_support (g : ℕ → ℝ)
    (hg : Function.HasFiniteSupport g) : Integrable g (poissonLaw rate) := by
  rw [poissonLaw, integrable_poissonMeasure_iff]
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset hg
  intro n hn
  change Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ n / (n.factorial : ℝ) * ‖g n‖ ≠ 0 at hn
  change g n ≠ 0
  intro hz
  simp [hz] at hn

/-- A finite-support real function belongs to Poisson L². -/
theorem memLp_two_of_finite_support (g : ℕ → ℝ)
    (hg : Function.HasFiniteSupport g) : MemLp g 2 (poissonLaw rate) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  apply integrable_of_finite_support rate
  apply Set.Finite.subset hg
  intro n hn
  change g n ^ 2 ≠ 0 at hn
  change g n ≠ 0
  intro hz
  simp [hz] at hn

/-- Genuine L² membership for a finite-support scalar field. -/
theorem finsupp_memLp_two (f : ℕ →₀ ℝ) :
    MemLp (fun n => f n) 2 (poissonLaw rate) :=
  memLp_two_of_finite_support rate f f.hasFiniteSupport

/-- Genuine L² membership for the Poisson forward difference. -/
theorem difference_memLp_two (f : ℕ →₀ ℝ) :
    MemLp (forwardDifference f) 2 (poissonLaw rate) :=
  memLp_two_of_finite_support rate _ (difference_hasFiniteSupport f)

/-- Genuine L² membership for the Poisson divergence expression. -/
theorem divergence_memLp_two (u : ℕ →₀ ℝ) :
    MemLp (poissonDivergenceExpr rate u) 2 (poissonLaw rate) :=
  memLp_two_of_finite_support rate _ (divergence_hasFiniteSupport rate u)

/-- An integrable Poisson integral equals its actual weighted convergent series. -/
theorem integral_eq_weighted_tsum (g : ℕ → ℝ)
    (hg : Integrable g (poissonLaw rate)) :
    (∫ n, g n ∂poissonLaw rate) = ∑' n, poissonWeight rate n * g n := by
  rw [poissonLaw, integral_poissonMeasure' hg]
  simp only [smul_eq_mul, poissonWeight, poissonLaw, poissonMeasure_real_singleton]

/-- Integrability of the left-hand side of the Poisson shift identity. -/
theorem count_mul_integrable (f : ℕ →₀ ℝ) :
    Integrable (fun n : ℕ => (n : ℝ) * f n) (poissonLaw rate) := by
  apply integrable_of_finite_support rate
  apply Set.Finite.subset f.hasFiniteSupport
  intro n hn
  change (n : ℝ) * f n ≠ 0 at hn
  change f n ≠ 0
  intro hz
  simp [hz] at hn

/-- Integrability of the shifted finite-support Poisson test function. -/
theorem shifted_integrable (f : ℕ →₀ ℝ) :
    Integrable (fun n => f (n + 1)) (poissonLaw rate) :=
  integrable_of_finite_support rate _ (shift_hasFiniteSupport f)

/-- The Poisson shift identity for actual integrable finite-support functions. -/
theorem poisson_shift_finsupp (f : ℕ →₀ ℝ) :
    (∫ n, (n : ℝ) * f n ∂poissonLaw rate) =
      (rate : ℝ) * ∫ n, f (n + 1) ∂poissonLaw rate := by
  rw [integral_eq_weighted_tsum rate _ (count_mul_integrable rate f),
    integral_eq_weighted_tsum rate _ (shifted_integrable rate f)]
  have hfin : Function.HasFiniteSupport
      (fun n => poissonWeight rate n * ((n : ℝ) * f n)) := by
    apply Set.Finite.subset f.hasFiniteSupport
    intro n hn
    change poissonWeight rate n * ((n : ℝ) * f n) ≠ 0 at hn
    change f n ≠ 0
    intro hz
    simp [hz] at hn
  have hs : Summable (fun n => poissonWeight rate n * ((n : ℝ) * f n)) :=
    summable_of_hasFiniteSupport hfin
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
  have ht : ∀ n : ℕ,
      poissonWeight rate (n + 1) * ((n + 1 : ℝ) * f (n + 1)) =
        (rate : ℝ) * (poissonWeight rate n * f (n + 1)) := by
    intro n
    calc
      poissonWeight rate (n + 1) * ((n + 1 : ℝ) * f (n + 1)) =
          ((n + 1 : ℝ) * poissonWeight rate (n + 1)) * f (n + 1) := by ring
      _ = (rate : ℝ) * (poissonWeight rate n * f (n + 1)) := by
        rw [poisson_weight_succ]
        ring
  simp only [Nat.cast_add, Nat.cast_one]
  simp_rw [ht]
  rw [tsum_mul_left]

/-- The product of two finite-support functions is finite-support. -/
theorem pairing_hasFiniteSupport (f : ℕ →₀ ℝ) (g : ℕ → ℝ) :
    Function.HasFiniteSupport (fun n => f n * g n) := by
  apply Set.Finite.subset f.hasFiniteSupport
  intro n hn
  change f n * g n ≠ 0 at hn
  change f n ≠ 0
  intro hz
  simp [hz] at hn

/-- Both finite-support pairing integrands are genuinely Poisson-integrable. -/
theorem difference_pairing_integrable (f u : ℕ →₀ ℝ) :
    Integrable (fun n => forwardDifference f n * u n) (poissonLaw rate) := by
  apply integrable_of_finite_support rate
  apply Set.Finite.subset u.hasFiniteSupport
  intro n hn
  change forwardDifference f n * u n ≠ 0 at hn
  change u n ≠ 0
  intro hz
  simp [hz] at hn

theorem divergence_pairing_integrable (f u : ℕ →₀ ℝ) :
    Integrable (fun n => f n * poissonDivergenceExpr rate u n) (poissonLaw rate) :=
  integrable_of_finite_support rate _ (pairing_hasFiniteSupport f _)

/-- Both pairings also belong to Poisson L² because their supports are finite. -/
theorem difference_pairing_memLp_two (f u : ℕ →₀ ℝ) :
    MemLp (fun n => forwardDifference f n * u n) 2 (poissonLaw rate) := by
  apply memLp_two_of_finite_support rate
  apply Set.Finite.subset u.hasFiniteSupport
  intro n hn
  change forwardDifference f n * u n ≠ 0 at hn
  change u n ≠ 0
  intro hz
  simp [hz] at hn

theorem divergence_pairing_memLp_two (f u : ℕ →₀ ℝ) :
    MemLp (fun n => f n * poissonDivergenceExpr rate u n) 2 (poissonLaw rate) :=
  memLp_two_of_finite_support rate _ (pairing_hasFiniteSupport f _)

/-- The cross term reindexes by one count, with zero at the count-zero boundary. -/
theorem poisson_shift_pairing_finsupp (f u : ℕ →₀ ℝ) :
    (rate : ℝ) * (∫ n, f (n + 1) * u n ∂poissonLaw rate) =
      ∫ n, f n * backwardWeighted u n ∂poissonLaw rate := by
  have hshift : Integrable (fun n => f (n + 1) * u n) (poissonLaw rate) := by
    apply integrable_of_finite_support rate
    apply Set.Finite.subset u.hasFiniteSupport
    intro n hn
    change f (n + 1) * u n ≠ 0 at hn
    change u n ≠ 0
    intro hz
    simp [hz] at hn
  have hback : Integrable (fun n => f n * backwardWeighted u n) (poissonLaw rate) :=
    integrable_of_finite_support rate _ (pairing_hasFiniteSupport f _)
  rw [integral_eq_weighted_tsum rate _ hshift,
    integral_eq_weighted_tsum rate _ hback]
  have hfin : Function.HasFiniteSupport
      (fun n => poissonWeight rate n * (f n * backwardWeighted u n)) := by
    apply Set.Finite.subset f.hasFiniteSupport
    intro n hn
    change poissonWeight rate n * (f n * backwardWeighted u n) ≠ 0 at hn
    change f n ≠ 0
    intro hz
    simp [hz] at hn
  have hs : Summable (fun n => poissonWeight rate n * (f n * backwardWeighted u n)) :=
    summable_of_hasFiniteSupport hfin
  rw [hs.tsum_eq_zero_add]
  simp only [backwardWeighted, mul_zero, zero_add]
  have ht : ∀ n : ℕ,
      poissonWeight rate (n + 1) *
          (f (n + 1) * backwardWeighted u (n + 1)) =
        (rate : ℝ) * (poissonWeight rate n * (f (n + 1) * u n)) := by
    intro n
    simp only [backwardWeighted]
    calc
      poissonWeight rate (n + 1) * (f (n + 1) * ((n + 1 : ℝ) * u n)) =
          ((n + 1 : ℝ) * poissonWeight rate (n + 1)) *
            (f (n + 1) * u n) := by ring
      _ = (rate : ℝ) * (poissonWeight rate n * (f (n + 1) * u n)) := by
        rw [poisson_weight_succ]
        ring
  change (rate : ℝ) * (∑' n, poissonWeight rate n * (f (n + 1) * u n)) =
    ∑' n, poissonWeight rate (n + 1) *
      (f (n + 1) * backwardWeighted u (n + 1))
  simp_rw [ht]
  rw [tsum_mul_left]
/-- Actual finite-support Poisson integration by parts, with both integrands
proved integrable independently. The count-zero backward term is zero. -/
theorem poisson_difference_ibp_finsupp (f u : ℕ →₀ ℝ) :
    (rate : ℝ) * (∫ n, forwardDifference f n * u n ∂poissonLaw rate) =
      ∫ n, f n * poissonDivergenceExpr rate u n ∂poissonLaw rate := by
  have hshift : Integrable (fun n => f (n + 1) * u n) (poissonLaw rate) := by
    apply integrable_of_finite_support rate
    apply Set.Finite.subset u.hasFiniteSupport
    intro n hn
    change f (n + 1) * u n ≠ 0 at hn
    change u n ≠ 0
    intro hz
    simp [hz] at hn
  have hdiag : Integrable (fun n => f n * u n) (poissonLaw rate) :=
    integrable_of_finite_support rate _ (pairing_hasFiniteSupport f _)
  have hback : Integrable (fun n => f n * backwardWeighted u n) (poissonLaw rate) :=
    integrable_of_finite_support rate _ (pairing_hasFiniteSupport f _)
  have hleft : (∫ n, forwardDifference f n * u n ∂poissonLaw rate) =
      (∫ n, f (n + 1) * u n ∂poissonLaw rate) -
        ∫ n, f n * u n ∂poissonLaw rate := by
    simp only [forwardDifference, sub_mul]
    exact integral_sub hshift hdiag
  have hright : (∫ n, f n * poissonDivergenceExpr rate u n ∂poissonLaw rate) =
      (∫ n, f n * backwardWeighted u n ∂poissonLaw rate) -
        (rate : ℝ) * ∫ n, f n * u n ∂poissonLaw rate := by
    have hpoint : ∀ n : ℕ,
        f n * poissonDivergenceExpr rate u n =
          f n * backwardWeighted u n - (rate : ℝ) * (f n * u n) := by
      intro n
      unfold poissonDivergenceExpr
      ring
    simp_rw [hpoint]
    rw [integral_sub hback (hdiag.const_mul _), integral_const_mul]
  rw [hleft, hright, mul_sub, poisson_shift_pairing_finsupp]

/-- The actual finite difference of the pointwise product has the
additional quadratic difference term characteristic of jump calculus. -/
theorem poisson_difference_mul_finsupp (f g : ℕ →₀ ℝ) (n : ℕ) :
    forwardDifference (f * g) n =
      f n * forwardDifference g n + g n * forwardDifference f n +
        forwardDifference f n * forwardDifference g n := by
  simp only [forwardDifference, Finsupp.mul_apply]
  ring

/-- The difference belongs to the rate-weighted Poisson integrand L² space. -/
theorem difference_memLp_two_weighted (f : ℕ →₀ ℝ) :
    MemLp (forwardDifference f) 2 ((rate : ℝ≥0∞) • poissonLaw rate) :=
  (difference_memLp_two rate f).smul_measure (by finiteness)

/-- A finite-support vector belongs to the rate-weighted Poisson L² space. -/
theorem finsupp_memLp_two_weighted (u : ℕ →₀ ℝ) :
    MemLp (fun n => u n) 2 ((rate : ℝ≥0∞) • poissonLaw rate) :=
  (finsupp_memLp_two rate u).smul_measure (by finiteness)

/-- Both pairing integrands also belong to the weighted integrand L² space. -/
theorem difference_pairing_memLp_two_weighted (f u : ℕ →₀ ℝ) :
    MemLp (fun n => forwardDifference f n * u n) 2
      ((rate : ℝ≥0∞) • poissonLaw rate) :=
  (difference_pairing_memLp_two rate f u).smul_measure (by finiteness)

theorem divergence_pairing_memLp_two_weighted (f u : ℕ →₀ ℝ) :
    MemLp (fun n => f n * poissonDivergenceExpr rate u n) 2
      ((rate : ℝ≥0∞) • poissonLaw rate) :=
  (divergence_pairing_memLp_two rate f u).smul_measure (by finiteness)

end OperatorDerivativeRewrite.Foundation.PoissonDifferenceCore
