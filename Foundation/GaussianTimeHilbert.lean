import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Deterministic time vectors for a Gaussian process

The time Hilbert space is actual Lebesgue L² on the real line.  Nonnegative
times are represented by indicators of `(0,t]`; no stochastic process or
sample-path regularity is assumed here.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace OperatorDerivativeRewrite.Foundation.GaussianTimeHilbert

/-- The real Hilbert space used for deterministic time functions. -/
abbrev TimeHilbert := Lp ℝ 2 (volume : Measure ℝ)

/-- Completeness comes from the complete scalar space and the Lp construction. -/
theorem timeHilbert_complete : CompleteSpace TimeHilbert := inferInstance

/-- Lebesgue measure is separable, so the actual L² space is second countable. -/
theorem timeHilbert_secondCountable : SecondCountableTopology TimeHilbert := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  infer_instance

/-- Any finite interval indicator belongs to Lebesgue L², including empty intervals. -/
theorem interval_indicator_memLp (a b : ℝ) :
    MemLp ((Ioc a b).indicator fun _ : ℝ => (1 : ℝ)) 2 volume :=
  memLp_indicator_const 2 measurableSet_Ioc 1 (Or.inr (by simp [Real.volume_Ioc]))

/-- The L² equivalence class of the indicator of `(a,b]`. -/
def intervalVector (a b : ℝ) : TimeHilbert :=
  indicatorConstLp 2 (measurableSet_Ioc (a := a) (b := b))
    (by simp [Real.volume_Ioc]) 1

theorem intervalVector_coeFn (a b : ℝ) :
    (intervalVector a b : ℝ → ℝ) =ᵐ[volume] (Ioc a b).indicator fun _ => 1 :=
  indicatorConstLp_coeFn

/-- The time vector at a nonnegative time is the indicator of `(0,t]`. -/
def timeVector (t : ℝ≥0) : TimeHilbert := intervalVector 0 t

theorem timeVector_coeFn (t : ℝ≥0) :
    (timeVector t : ℝ → ℝ) =ᵐ[volume] (Ioc 0 (t : ℝ)).indicator fun _ => 1 :=
  intervalVector_coeFn 0 t

theorem timeVector_zero : timeVector 0 = 0 := by
  apply Lp.ext
  filter_upwards [timeVector_coeFn 0, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume)]
    with x hx hz
  simpa using hx

theorem intervalVector_inner (a b c d : ℝ) :
    inner ℝ (intervalVector a b) (intervalVector c d) =
      volume.real (Ioc a b ∩ Ioc c d) :=
  L2.real_inner_indicatorConstLp_one_indicatorConstLp_one _ _ _ _

/-- The covariance kernel of the deterministic time vectors is `min`. -/
theorem timeVector_inner (s t : ℝ≥0) :
    inner ℝ (timeVector s) (timeVector t) = min (s : ℝ) (t : ℝ) := by
  rw [timeVector, timeVector, intervalVector_inner, Ioc_inter_Ioc]
  simp only [max_self, Measure.real, Real.volume_Ioc, sub_zero]
  exact ENNReal.toReal_ofReal (le_min s.coe_nonneg t.coe_nonneg)

theorem timeVector_norm_sq (t : ℝ≥0) : ‖timeVector t‖ ^ 2 = (t : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, timeVector_inner, min_self]

/-- Subtracting two nested time indicators gives the interval increment. -/
theorem timeVector_sub (s t : ℝ≥0) (hst : s ≤ t) :
    timeVector t - timeVector s = intervalVector s t := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (timeVector t) (timeVector s), timeVector_coeFn t,
    timeVector_coeFn s, intervalVector_coeFn s t] with x hsub ht hs hi
  rw [hsub, Pi.sub_apply, ht, hs, hi]
  have hst' : (s : ℝ) ≤ t := hst
  have hs0 := s.coe_nonneg
  simp only [Set.indicator, mem_Ioc]
  split_ifs <;> simp_all
  all_goals
    have hstR : (s : ℝ) ≤ (t : ℝ) := hst
    have hsR : (0 : ℝ) ≤ (s : ℝ) := s.coe_nonneg
    linarith

theorem timeVector_sub_coeFn (s t : ℝ≥0) (hst : s ≤ t) :
    (timeVector t - timeVector s : TimeHilbert) =ᵐ[volume]
      (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => (1 : ℝ)) := by
  rw [timeVector_sub s t hst]
  exact intervalVector_coeFn s t

theorem timeVector_sub_norm_sq (s t : ℝ≥0) (hst : s ≤ t) :
    ‖timeVector t - timeVector s‖ ^ 2 = (t : ℝ) - s := by
  rw [timeVector_sub s t hst, ← real_inner_self_eq_norm_sq, intervalVector_inner,
    inter_self]
  simp only [Measure.real, Real.volume_Ioc]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr hst)

/-- Indicators of disjoint intervals are orthogonal in the actual time Hilbert space. -/
theorem intervalVector_inner_eq_zero_of_disjoint (a b c d : ℝ)
    (h : Disjoint (Ioc a b) (Ioc c d)) :
    inner ℝ (intervalVector a b) (intervalVector c d) = 0 := by
  rw [intervalVector_inner, Set.disjoint_iff_inter_eq_empty.mp h]
  simp

theorem timeVector_increments_orthogonal (a b c d : ℝ≥0)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    inner ℝ (timeVector b - timeVector a) (timeVector d - timeVector c) = 0 := by
  rw [timeVector_sub a b hab, timeVector_sub c d hcd]
  apply intervalVector_inner_eq_zero_of_disjoint
  refine Set.disjoint_left.mpr ?_
  intro x hx hy
  exact (not_lt_of_ge (le_trans hx.2 hbc)) hy.1

end OperatorDerivativeRewrite.Foundation.GaussianTimeHilbert
