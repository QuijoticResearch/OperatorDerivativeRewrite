import Foundation.GaussianDampedReflectedIto
import Mathlib.Analysis.Calculus.SmoothSeries

/-! A global C2 extension for completed damped Fourier means. Absolute weights
and squared-rate weights suffice; the intermediate rate bound is derived.
The original reflected Ito hypotheses are discharged without a new integral. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.ReflectedDampingSeries
open GaussianDampedReflectedIto
variable (b c : ℕ → ℝ)

def cost1 (k : ℕ) : ℝ := |b k| * c k
def cost2 (k : ℕ) : ℝ := |b k| * (c k)^2
def value (x : ℝ) : ℝ := ∑' k, b k * extension (c k) x
def first (x : ℝ) : ℝ := ∑' k, b k * slope (c k) x
def second (x : ℝ) : ℝ := ∑' k, b k * curvature (c k) x

variable (hc : ∀ k, 0 ≤ c k) (hb : Summable (fun k => |b k|))
  (h2 : Summable (cost2 b c))

include hc hb h2 in
theorem cost1_summable : Summable (cost1 b c) := by
  apply (hb.add h2).of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (hc k))
  intro k
  have h : c k ≤ 1 + (c k)^2 := by nlinarith [sq_nonneg (c k - 1/2)]
  simpa only [cost1, cost2, mul_add, mul_one] using
    mul_le_mul_of_nonneg_left h (abs_nonneg (b k))

include hc
theorem first_term_bound (k : ℕ) (x : ℝ) :
    ‖b k * slope (c k) x‖ ≤ 2 * cost1 b c k := by
  rw [norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (slope_bound (hc k) x) (abs_nonneg _)).trans_eq
    (by unfold cost1; ring)

theorem second_term_bound (k : ℕ) (x : ℝ) :
    ‖b k * curvature (c k) x‖ ≤ cost2 b c k := by
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (curvature_bound (hc k) x) (abs_nonneg _)

include hb h2
theorem value_hasDerivAt (x : ℝ) : HasDerivAt (value b c) (first b c x) x := by
  apply hasDerivAt_tsum (y₀ := (0 : ℝ)) ((cost1_summable b c hc hb h2).mul_left 2)
    (fun k y => (extension_hasDerivAt (c k) y).const_mul (b k))
    (first_term_bound b c hc)
  have h : Summable b := (show Summable (fun k => ‖b k‖) by
    simpa only [Real.norm_eq_abs] using hb).of_norm
  simpa only [extension_zero, mul_one] using h

theorem first_hasDerivAt (x : ℝ) : HasDerivAt (first b c) (second b c x) x := by
  apply hasDerivAt_tsum (y₀ := (0 : ℝ)) h2
    (fun k y => (slope_hasDerivAt (c k) y).const_mul (b k))
    (second_term_bound b c hc)
  exact ((cost1_summable b c hc hb h2).mul_left 2).of_norm_bounded
    (fun k => first_term_bound b c hc k 0)

theorem value_deriv : deriv (value b c) = first b c :=
  funext fun x => (value_hasDerivAt b c hc hb h2 x).deriv

theorem value_second : deriv (deriv (value b c)) = second b c := by
  rw [value_deriv b c hc hb h2]
  exact funext fun x => (first_hasDerivAt b c hc hb h2 x).deriv

theorem value_C2 : ContDiff ℝ 2 (value b c) := by
  have hs : Continuous (second b c) := by
    apply continuous_tsum (fun k => ?_) h2 (second_term_bound b c hc)
    unfold curvature
    fun_prop
  have hfirst : ContDiff ℝ 1 (first b c) := contDiff_one_iff_deriv.mpr
    ⟨fun x => (first_hasDerivAt b c hc hb h2 x).differentiableAt, by
      rw [show deriv (first b c) = second b c from
        funext fun x => (first_hasDerivAt b c hc hb h2 x).deriv]
      exact hs⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  exact ⟨fun x => (value_hasDerivAt b c hc hb h2 x).differentiableAt,
    by simp, by rw [value_deriv b c hc hb h2]; exact hfirst⟩

theorem first_bound (x : ℝ) : ‖first b c x‖ ≤ 2 * ∑' k, cost1 b c k := by
  have h := ((cost1_summable b c hc hb h2).mul_left 2).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun k => first_term_bound b c hc k x)
  apply (norm_tsum_le_tsum_norm h).trans
  simpa only [tsum_mul_left] using h.tsum_le_tsum
    (fun k => first_term_bound b c hc k x) ((cost1_summable b c hc hb h2).mul_left 2)

omit hb in
theorem second_bound (x : ℝ) : ‖second b c x‖ ≤ ∑' k, cost2 b c k := by
  have h := h2.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => second_term_bound b c hc k x)
  exact (norm_tsum_le_tsum_norm h).trans
    (h.tsum_le_tsum (fun k => second_term_bound b c hc k x) h2)

theorem first_uniform :
    TendstoUniformly (fun n x => ∑ k ∈ Finset.range n, b k * slope (c k) x)
      (first b c) atTop :=
  tendstoUniformly_tsum_nat ((cost1_summable b c hc hb h2).mul_left 2)
    (first_term_bound b c hc)

omit hb in
theorem second_uniform :
    TendstoUniformly (fun n x => ∑ k ∈ Finset.range n, b k * curvature (c k) x)
      (second b c) atTop :=
  tendstoUniformly_tsum_nat h2 (second_term_bound b c hc)

omit hc hb h2
theorem value_nonneg {x : ℝ} (hx : 0 ≤ x) :
    value b c x = ∑' k, b k * Real.exp (-c k * x) := by
  apply tsum_congr
  intro k
  rw [extension_nonneg (c k) hx]

theorem value_zero : value b c 0 = ∑' k, b k := by simp only [value, extension_zero, mul_one]

theorem first_zero : first b c 0 = -(∑' k, b k * c k) := by
  simp only [first, slope_zero, mul_neg, tsum_neg]

end OperatorDerivativeRewrite.Foundation.ReflectedDampingSeries
