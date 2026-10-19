import Foundation.IBMFullSchwartzTerminal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! Physical two-sided Brownian indicator coordinates in actual Lebesgue L2.
Their span is dense, proved using the Lebesgue differentiation theorem. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalNoiseVectors
open GaussianTimeHilbert

/-- Oriented Brownian kernel, including the negative half-line. -/
def vector (r : ℝ) : TimeHilbert := intervalVector 0 r-intervalVector r 0

theorem vector_coeFn (r : ℝ) : vector r =ᵐ[volume] fun x =>
    (if x ≤ r then (1 : ℝ) else 0)-(if x ≤ 0 then 1 else 0) := by
  filter_upwards [Lp.coeFn_sub (intervalVector 0 r) (intervalVector r 0),
    intervalVector_coeFn 0 r, intervalVector_coeFn r 0] with x hs hp hn
  rw [vector, hs, Pi.sub_apply, hp, hn]
  simp only [indicator, mem_Ioc]
  split_ifs <;> simp_all <;> linarith

theorem vector_zero : vector 0 = 0 := sub_self _

theorem vector_sub {a b : ℝ} (hab : a ≤ b) :
    vector b-vector a = intervalVector a b := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (vector b) (vector a), vector_coeFn b,
    vector_coeFn a, intervalVector_coeFn a b] with x hs hb ha hi
  rw [hs, Pi.sub_apply, hb, ha, hi]
  simp only [indicator, mem_Ioc]
  split_ifs <;> simp_all <;> linarith

theorem interval_norm_sq {a b : ℝ} (hab : a ≤ b) :
    ‖intervalVector a b‖^2 = b-a := by
  rw [← real_inner_self_eq_norm_sq, intervalVector_inner, inter_self]
  simp only [Measure.real, Real.volume_Ioc]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr hab)

theorem vector_norm_sq (r : ℝ) : ‖vector r‖^2 = |r| := by
  by_cases hr : 0 ≤ r
  · have he := vector_sub hr
    rw [vector_zero, sub_zero] at he
    rw [he, interval_norm_sq hr, sub_zero, abs_of_nonneg hr]
  · have hr' := le_of_lt (lt_of_not_ge hr)
    have he := vector_sub hr'
    rw [vector_zero, zero_sub] at he
    have hn := interval_norm_sq hr'
    rw [← he, norm_neg, zero_sub] at hn
    rw [hn, abs_of_neg (lt_of_not_ge hr)]

theorem vector_increment_sq (s r : ℝ) : ‖vector r-vector s‖^2 = |r-s| := by
  rcases le_total s r with h | h
  · rw [vector_sub h, interval_norm_sq h, abs_of_nonneg (sub_nonneg.mpr h)]
  · rw [norm_sub_rev, vector_sub h, interval_norm_sq h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring

/-- The Hilbert pairing is the actual oriented physical-space integral. -/
theorem vector_inner_integral (f : TimeHilbert) (r : ℝ) :
    inner ℝ (vector r) f = ∫ x in 0..r, f x := by
  have hi (a b : ℝ) : inner ℝ (intervalVector a b) f = ∫ x in Ioc a b, f x := by
    rw [L2_inner_eq_integral]
    calc
      _ = ∫ x, (Ioc a b).indicator (fun x => f x) x := by
        apply integral_congr_ae
        filter_upwards [intervalVector_coeFn a b] with x hx
        rw [hx]
        simp only [Real.inner_apply]
        by_cases h : x ∈ Ioc a b <;> simp [h]
      _ = _ := integral_indicator measurableSet_Ioc
  rw [vector, inner_sub_left, hi, hi]
  rfl

/-- No density assumption is imposed on the physical kernels. -/
theorem span_dense : (Submodule.span ℝ (Set.range vector)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm ?_ bot_le
  intro f hf
  have hz (r : ℝ) : (∫ x in 0..r, f x) = 0 := by
    rw [← vector_inner_integral]
    exact hf _ (Submodule.subset_span ⟨r,rfl⟩)
  have he : (fun r => ∫ x in 0..r, f x) = fun _ => (0 : ℝ) := funext hz
  have hd := LocallyIntegrable.ae_hasDerivAt_integral
    ((Lp.memLp f).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hzero : f =ᵐ[volume] fun _ => (0 : ℝ) := by
    filter_upwards [hd] with x hx
    have hh := hx 0
    rw [he] at hh
    exact hh.unique (hasDerivAt_const x (0 : ℝ))
  have hf0 : f=0 := by
    apply Lp.ext
    exact hzero.trans (Lp.coeFn_zero ℝ 2 volume).symm
  simp [hf0]

end OperatorDerivativeRewrite.Foundation.IBMPhysicalNoiseVectors
