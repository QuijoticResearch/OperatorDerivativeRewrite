import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
/-! Exponential Laplace decay excludes positive spectral mass below the decay rate. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.YMSpectralLaplaceBridge

theorem interval_lower (μ : Measure ℝ) [IsFiniteMeasure μ] (b t : ℝ) (ht : 0 ≤ t)
    (hI : Integrable (fun x : ℝ => Real.exp (-t*x)) μ) :
    Real.exp (-t*b) * (μ (Set.Iio b)).toReal ≤
      ∫ x : ℝ, Real.exp (-t*x) ∂μ := by
  have hJ : Integrable ((Set.Iio b).indicator (fun _ : ℝ => Real.exp (-t*b))) μ :=
    (integrable_const _).indicator measurableSet_Iio
  have hpoint : (Set.Iio b).indicator (fun _ : ℝ => Real.exp (-t*b)) ≤
      (fun x : ℝ => Real.exp (-t*x)) := by
    intro x
    by_cases hx : x < b
    · rw [Set.indicator_of_mem (show x ∈ Set.Iio b from hx)]
      exact Real.exp_le_exp.mpr (by nlinarith)
    · rw [Set.indicator_of_notMem (show x ∉ Set.Iio b from hx)]
      exact (Real.exp_pos _).le
  have h := integral_mono hJ hI hpoint
  simpa [integral_indicator, integral_const, smul_eq_mul, mul_comm, measureReal_def] using h

theorem no_mass_below (μ : Measure ℝ) [IsFiniteMeasure μ]
    (m C b : ℝ) (hb : b < m)
    (hI : ∀ n : ℕ, Integrable (fun x : ℝ => Real.exp (-(n:ℝ)*x)) μ)
    (hU : ∀ n : ℕ, (∫ x : ℝ, Real.exp (-(n:ℝ)*x) ∂μ) ≤
      C * Real.exp (-m*(n:ℝ))) :
    μ (Set.Iio b) = 0 := by
  let q : ℝ := Real.exp (-(m-b))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [show (1:ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hbound (n : ℕ) : (μ (Set.Iio b)).toReal ≤ C * q^n := by
    have hL := interval_lower μ b n (by positivity) (hI n)
    have hU' := hU n
    have hR : C * Real.exp (-m*(n:ℝ)) =
        Real.exp (-(n:ℝ)*b) * (C*q^n) := by
      rw [show q^n = Real.exp (-(m-b)*(n:ℝ)) by
        change Real.exp (-(m-b)) ^ n = _
        rw [← Real.exp_nat_mul]
        congr 1
        ring]
      calc
        C * Real.exp (-m*(n:ℝ)) = C * Real.exp (-(n:ℝ)*b + -(m-b)*(n:ℝ)) := by congr 1; ring
        _ = C * (Real.exp (-(n:ℝ)*b) * Real.exp (-(m-b)*(n:ℝ))) := by rw [Real.exp_add]
        _ = Real.exp (-(n:ℝ)*b) * (C * Real.exp (-(m-b)*(n:ℝ))) := by ring
    rw [hR] at hU'
    exact le_of_mul_le_mul_left (hL.trans hU') (Real.exp_pos _)
  have hlimq : Filter.Tendsto (fun n : ℕ => q^n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hlim : Filter.Tendsto (fun n : ℕ => C*q^n) Filter.atTop (nhds 0) := by
    convert tendsto_const_nhds.mul hlimq using 1; simp
  have hmass : (μ (Set.Iio b)).toReal ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  have hzero : (μ (Set.Iio b)).toReal = 0 := le_antisymm hmass (ENNReal.toReal_nonneg)
  exact (ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right
    (ne_of_lt (measure_lt_top μ _))
theorem no_mass_below_gap (μ : Measure ℝ) [IsFiniteMeasure μ]
    (m C : ℝ)
    (hI : ∀ n : ℕ, Integrable (fun x : ℝ => Real.exp (-(n:ℝ)*x)) μ)
    (hU : ∀ n : ℕ, (∫ x : ℝ, Real.exp (-(n:ℝ)*x) ∂μ) ≤
      C * Real.exp (-m*(n:ℝ))) :
    μ (Set.Iio m) = 0 := by
  have hcover : Set.Iio m = ⋃ n : ℕ, Set.Iio (m - 1 / ((n:ℝ)+1)) := by
    ext x
    constructor
    · intro hx
      change x < m at hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_⟩
      change x < m - 1 / ((n:ℝ)+1)
      linarith
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
      have hp : 0 < 1 / ((n:ℝ)+1) := by positivity
      change x < m - 1 / ((n:ℝ)+1) at hn
      exact lt_trans hn (sub_lt_self m hp)
  rw [hcover]
  exact measure_iUnion_null (fun n =>
    no_mass_below μ m C (m - 1 / ((n:ℝ)+1)) (sub_lt_self m (by positivity)) hI hU)
end OperatorDerivativeRewrite.Foundation.YMSpectralLaplaceBridge
