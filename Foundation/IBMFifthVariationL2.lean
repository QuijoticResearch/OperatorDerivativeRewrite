import Foundation.IBMActualIncrementMoments
import Foundation.IBMUniformFifthRemainder

/-! Actual tenth moments control the total fifth variation in L2.
No independence of increments is used in the finite Cauchy--Schwarz bound. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMFifthVariationL2
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy
open IBMUniformFifthRemainder IBMActualIncrementMoments GaussianAbsoluteMoments
attribute [local irreducible] ibmValue clockPath sceneryPath

def increment (T : ℝ≥0) (n k : ℕ) (ω : JointSample) : ℝ :=
  |ibmValue (grid (T / (n + 1)) (k + 1)) ω -
    ibmValue (grid (T / (n + 1)) k) ω|^5

theorem increment_memLp (T : ℝ≥0) (n k : ℕ) :
    MemLp (increment T n k) 2 jointMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (increment_measurable _ _ 5).aestronglyMeasurable).mpr
  simpa only [increment, Real.norm_eq_abs, sq_abs, ← pow_mul] using
    actual_even_integrable (grid (T / (n + 1)) k)
      (grid (T / (n + 1)) (k + 1)) 5

theorem fifth_memLp (T : ℝ≥0) (n : ℕ) : MemLp (fifth T n) 2 jointMeasure := by
  exact memLp_finsetSum _ (fun k _ => increment_memLp T n k)

theorem fifth_measurable (T : ℝ≥0) (n : ℕ) : Measurable (fifth T n) := by
  apply Finset.measurable_sum
  intro k hk
  exact increment_measurable _ _ 5

theorem squared_bound (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    (fifth T n ω)^2 ≤ (n + 1 : ℝ) *
      ∑ k ∈ Finset.range (n + 1), (increment T n k ω)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1))
    (fun k => increment T n k ω) (fun _ => (1 : ℝ))
  simpa only [mul_one, one_mul, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_comm, Nat.cast_add, Nat.cast_one, fifth, increment] using h

theorem increment_squared_integral (T : ℝ≥0) (n k : ℕ) :
    (∫ ω, (increment T n k ω)^2 ∂jointMeasure) ≤
      standardMoment 10 * (Real.sqrt ((T : ℝ)/(n+1)))^5 * standardMoment 5 := by
  have h := actual_even_moment_le (grid (T / (n + 1)) k)
    (grid (T / (n + 1)) (k + 1)) 5
  have hd : |(grid (T / (n + 1)) (k + 1) : ℝ)-grid (T / (n + 1)) k| =
      (T : ℝ)/(n+1) := by
    simp only [grid, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
      Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
    rw [show (T : ℝ)/(n+1)*(k+1)-(T : ℝ)/(n+1)*k = (T : ℝ)/(n+1) by ring,
      abs_of_nonneg (by positivity)]
  simpa only [increment, ← pow_mul, hd] using h

/-- A genuine squared L2 estimate, of order N^(-1/2), for the original law. -/
theorem fifth_squared_integral_bound (T : ℝ≥0) (n : ℕ) :
    (∫ ω, (fifth T n ω)^2 ∂jointMeasure) ≤
      (standardMoment 10 * standardMoment 5) * (T : ℝ)^2 *
        Real.sqrt ((T : ℝ)/(n+1)) := by
  have hi (k : ℕ) : Integrable (fun ω => (increment T n k ω)^2) jointMeasure := by
    simpa only [increment, Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (increment_measurable _ _ 5).aestronglyMeasurable).mp
        (increment_memLp T n k)
  have hf : Integrable (fun ω => (fifth T n ω)^2) jointMeasure := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (fifth_measurable T n).aestronglyMeasurable).mp
        (fifth_memLp T n)
  have hb := integral_mono hf ((integrable_finsetSum _ (fun k _ => hi k)).const_mul
    (n+1 : ℝ)) (squared_bound T n)
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => hi k)] at hb
  have hs := Finset.sum_le_sum (s := Finset.range (n+1))
    (fun k _ => increment_squared_integral T n k)
  have h := hb.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at h
  have he : (n+1 : ℝ) * ((n+1 : ℝ) *
      (standardMoment 10 * (Real.sqrt ((T : ℝ)/(n+1)))^5 * standardMoment 5)) =
      (standardMoment 10 * standardMoment 5) * (T : ℝ)^2 *
        Real.sqrt ((T : ℝ)/(n+1)) := by
    have hsq := Real.sq_sqrt (show 0 ≤ (T : ℝ)/(n+1) by positivity)
    have hn : (n+1 : ℝ) ≠ 0 := by positivity
    calc
      _ = (standardMoment 10 * standardMoment 5) *
          ((n+1 : ℝ) * ((Real.sqrt ((T : ℝ)/(n+1)))^2))^2 *
          Real.sqrt ((T : ℝ)/(n+1)) := by ring
      _ = _ := by rw [hsq, mul_div_cancel₀ _ hn]
  exact h.trans_eq he

theorem fifth_squared_integral_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (fifth T n ω)^2 ∂jointMeasure) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (T : ℝ)/(n+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ _
      tendsto_natCast_atTop_atTop)
  apply squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _)
    (fifth_squared_integral_bound T)
  simpa using ((ht.sqrt).const_mul ((standardMoment 10 * standardMoment 5) * (T : ℝ)^2))

def fifthClass (T : ℝ≥0) (n : ℕ) : Lp ℝ 2 jointMeasure :=
  (fifth_memLp T n).toLp (fifth T n)

theorem fifthClass_actual_ae (T : ℝ≥0) (n : ℕ) :
    fifthClass T n =ᵐ[jointMeasure] fifth T n := (fifth_memLp T n).coeFn_toLp

theorem fifthClass_norm_sq (T : ℝ≥0) (n : ℕ) :
    ‖fifthClass T n‖^2 = ∫ ω, (fifth T n ω)^2 ∂jointMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fifthClass_actual_ae T n] with ω hω
  rw [hω, Real.inner_apply, pow_two]

theorem fifthClass_tendsto (T : ℝ≥0) :
    Tendsto (fifthClass T) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (fifth_squared_integral_tendsto T).sqrt
  simpa only [← fifthClass_norm_sq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

end OperatorDerivativeRewrite.Foundation.IBMFifthVariationL2
