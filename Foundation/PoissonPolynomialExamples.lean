import Foundation.PoissonMoments

/-! Low-order Poisson count polynomials as genuine Hilbert-space operator vectors. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonPolynomialExamples
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonWeightedDomains PoissonCoordinateEvaluation PoissonMoments
open PoissonBoundedCalculus

/-- The compensated one-site Poisson count. -/
def centeredCount (rate : ℝ≥0) (n : ℕ) : ℝ := n - rate

theorem centeredCount_memLp (rate : ℝ≥0) (hr : 0 < rate) :
    MemLp (centeredCount rate) 2 (poissonLaw rate) := by
  have hn := poisson_power_memLp_two rate hr 1
  have hc : MemLp (fun _ : ℕ => (rate : ℝ)) 2 (poissonLaw rate) := memLp_const _
  convert hn.sub hc using 1
  funext n
  simp [centeredCount]

theorem centeredCount_sq_memLp (rate : ℝ≥0) (hr : 0 < rate) :
    MemLp (fun n => (centeredCount rate n)^2) 2 (poissonLaw rate) := by
  have hp := polynomial_memLp_two rate hr
    ((Polynomial.X - Polynomial.C (rate : ℝ)) ^ 2)
  convert hp using 1
  funext n
  simp [centeredCount]

def centeredCountL2 (rate : ℝ≥0) (hr : 0 < rate) : ScalarL2 rate :=
  (centeredCount_memLp rate hr).toLp (centeredCount rate)

def centeredCountSqL2 (rate : ℝ≥0) (hr : 0 < rate) : ScalarL2 rate :=
  (centeredCount_sq_memLp rate hr).toLp (fun n => (centeredCount rate n)^2)

def constantOneField (rate : ℝ≥0) : FieldL2 rate :=
  (bounded_field_memLp rate (fun _ => 1) 1 (by simp)).toLp (fun _ => 1)

theorem centeredCountL2_apply (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    (centeredCountL2 rate hr) n = centeredCount rate n :=
  ae_eq_implies_pointwise rate hr
    (MemLp.coeFn_toLp (centeredCount_memLp rate hr)) n

theorem centeredCountSqL2_apply (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    (centeredCountSqL2 rate hr) n = (centeredCount rate n)^2 :=
  ae_eq_implies_pointwise rate hr
    (MemLp.coeFn_toLp (centeredCount_sq_memLp rate hr)) n

theorem constantOneField_apply (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    (constantOneField rate) n = 1 :=
  weighted_ae_eq_implies_pointwise rate hr
    (MemLp.coeFn_toLp (bounded_field_memLp rate (fun _ => 1) 1 (by simp))) n


/-- The compensated count has a square-integrable genuine forward difference. -/
theorem centeredCountL2_mem_difference_domain (rate : ℝ≥0) (hr : 0 < rate) :
    centeredCountL2 rate hr ∈ (maximalDifference rate hr).domain := by
  rw [mem_maximalDifference_domain_iff_memLp_difference rate hr]
  have hm := bounded_field_memLp rate (fun _ => 1) 1 (by simp)
  convert hm using 1
  funext n
  rw [centeredCountL2_apply rate hr, centeredCountL2_apply rate hr]
  simp [centeredCount]

/-- The constant field has square-integrable divergence, equal pointwise to the centered count. -/
theorem constantOneField_mem_divergence_domain (rate : ℝ≥0) (hr : 0 < rate) :
    constantOneField rate ∈ (maximalDivergence rate hr).domain := by
  rw [mem_maximalDivergence_domain_iff_memLp_divergence rate hr]
  convert centeredCount_memLp rate hr using 1
  funext n
  cases n with
  | zero =>
      simp [maximalDivergenceExpr, constantOneField_apply rate hr, centeredCount]
  | succ n =>
      simp [maximalDivergenceExpr, constantOneField_apply rate hr, centeredCount]

/-- The actual closed Poisson difference of the centered count is the constant field one. -/
theorem difference_centeredCount_eq_one (rate : ℝ≥0) (hr : 0 < rate) :
    (maximalDifference rate hr) ⟨centeredCountL2 rate hr,
      centeredCountL2_mem_difference_domain rate hr⟩ = constantOneField rate := by
  apply Lp.ext
  filter_upwards [] with n
  have hh := (maximalDifference rate hr).mem_graph
    ⟨centeredCountL2 rate hr, centeredCountL2_mem_difference_domain rate hr⟩
  rw [maximalDifference_graph] at hh
  rw [hh n, centeredCountL2_apply rate hr, centeredCountL2_apply rate hr,
    constantOneField_apply rate hr]
  simp [centeredCount]

/-- The actual closed Poisson divergence of the constant field is the compensated count. -/
theorem divergence_one_eq_centeredCount (rate : ℝ≥0) (hr : 0 < rate) :
    (maximalDivergence rate hr) ⟨constantOneField rate,
      constantOneField_mem_divergence_domain rate hr⟩ = centeredCountL2 rate hr := by
  apply Lp.ext
  filter_upwards [] with n
  have hh := (maximalDivergence rate hr).mem_graph
    ⟨constantOneField rate, constantOneField_mem_divergence_domain rate hr⟩
  rw [maximalDivergence_graph] at hh
  rw [hh n, centeredCountL2_apply rate hr]
  cases n with
  | zero =>
      simp [maximalDivergenceExpr, constantOneField_apply rate hr, centeredCount]
  | succ n =>
      simp [maximalDivergenceExpr, constantOneField_apply rate hr, centeredCount]

/-- The non-Gaussian square-rule expression is genuinely in weighted field L². -/
theorem centeredSquareGradient_memLp (rate : ℝ≥0) (hr : 0 < rate) :
    MemLp (fun n => 2 * centeredCount rate n + 1) 2
      ((rate : ℝ≥0∞) • poissonLaw rate) := by
  have hc := (centeredCount_memLp rate hr).smul_measure (by finiteness)
  have htwo := hc.const_mul (2 : ℝ)
  have hone := bounded_field_memLp rate (fun _ => 1) 1 (by simp)
  convert htwo.add hone using 1

/-- The compensated count squared lies in the exact maximal difference domain. -/
theorem centeredCountSqL2_mem_difference_domain (rate : ℝ≥0) (hr : 0 < rate) :
    centeredCountSqL2 rate hr ∈ (maximalDifference rate hr).domain := by
  rw [mem_maximalDifference_domain_iff_memLp_difference rate hr]
  convert centeredSquareGradient_memLp rate hr using 1
  funext n
  rw [centeredCountSqL2_apply rate hr, centeredCountSqL2_apply rate hr]
  simp only [centeredCount, Nat.cast_add, Nat.cast_one]
  ring

/-- The actual Poisson derivative has an extra term absent from ordinary calculus. -/
theorem difference_centeredCount_sq_apply (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    ((maximalDifference rate hr) ⟨centeredCountSqL2 rate hr,
      centeredCountSqL2_mem_difference_domain rate hr⟩) n =
      2 * centeredCount rate n + 1 := by
  have hh := (maximalDifference rate hr).mem_graph
    ⟨centeredCountSqL2 rate hr, centeredCountSqL2_mem_difference_domain rate hr⟩
  rw [maximalDifference_graph] at hh
  rw [hh n, centeredCountSqL2_apply rate hr, centeredCountSqL2_apply rate hr]
  simp only [centeredCount, Nat.cast_add, Nat.cast_one]
  ring

def centeredSquareGradientL2 (rate : ℝ≥0) (hr : 0 < rate) : FieldL2 rate :=
  (centeredSquareGradient_memLp rate hr).toLp
    (fun n => 2 * centeredCount rate n + 1)

/-- Operator equality for the finite-difference square rule. -/
theorem difference_centeredCount_sq_eq (rate : ℝ≥0) (hr : 0 < rate) :
    (maximalDifference rate hr) ⟨centeredCountSqL2 rate hr,
      centeredCountSqL2_mem_difference_domain rate hr⟩ =
        centeredSquareGradientL2 rate hr := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (centeredSquareGradient_memLp rate hr)] with n hn
  rw [difference_centeredCount_sq_apply rate hr n]
  exact hn.symm

/-- The ordinary differential square chain rule fails for the actual Poisson difference operator. -/
theorem ordinary_chain_rule_fails (rate : ℝ≥0) (hr : 0 < rate) :
    ¬ ∀ n : ℕ,
      ((maximalDifference rate hr) ⟨centeredCountSqL2 rate hr,
        centeredCountSqL2_mem_difference_domain rate hr⟩) n =
      2 * centeredCount rate n *
        ((maximalDifference rate hr) ⟨centeredCountL2 rate hr,
          centeredCountL2_mem_difference_domain rate hr⟩) n := by
  intro h
  have h0 := h 0
  have hd := congrArg (fun v : FieldL2 rate => v 0)
    (difference_centeredCount_eq_one rate hr)
  rw [constantOneField_apply rate hr] at hd
  rw [difference_centeredCount_sq_apply rate hr 0, hd] at h0
  linarith
end OperatorDerivativeRewrite.Foundation.PoissonPolynomialExamples
