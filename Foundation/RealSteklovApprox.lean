import Foundation.GaussianSobolevPrimitives
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! One-sided interval averaging: an explicit C2-to-C3 approximation.
The derivatives are proved from the ordinary FTC, not supplied as data. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal
namespace OperatorDerivativeRewrite.Foundation.RealSteklovApprox
open GaussianSobolevFixedSupport

def average (f : ℝ → ℝ) (e x : ℝ) : ℝ := (∫ y in x..(x+e), f y) / e

theorem average_eq_primitive (f : ℝ → ℝ) (hf : Continuous f) (e x : ℝ) :
    average f e x = (primitive 0 f (x+e) - primitive 0 f x) / e := by
  rw [average, primitive, primitive,
    intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

theorem average_hasDerivAt (f : ℝ → ℝ) (hf : Continuous f) (e x : ℝ) :
    HasDerivAt (average f e) ((f (x+e)-f x)/e) x := by
  have he : average f e = fun x => (primitive 0 f (x+e)-primitive 0 f x)/e :=
    funext (average_eq_primitive f hf e)
  rw [he]
  convert (((primitive_hasDerivAt hf 0 (x+e)).comp x
    ((hasDerivAt_id x).add_const e)).sub (primitive_hasDerivAt hf 0 x)).div_const e using 1 <;> simp

theorem average_deriv (f : ℝ → ℝ) (hf : Continuous f) (e : ℝ) :
    deriv (average f e) = fun x => (f (x+e)-f x)/e :=
  funext fun x => (average_hasDerivAt f hf e x).deriv

theorem average_contDiff_succ (f : ℝ → ℝ) {n : ℕ} (hf : ContDiff ℝ n f) (e : ℝ) :
    ContDiff ℝ (n+1) (average f e) := by
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x => (average_hasDerivAt f hf.continuous e x).differentiableAt, ?_, ?_⟩
  · simp
  · rw [average_deriv f hf.continuous]
    exact ((hf.comp (contDiff_id.add contDiff_const)).sub hf).div_const e

theorem deriv_average_eq_average_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (e : ℝ) :
    deriv (average f e) = average (deriv f) e := by
  rw [average_deriv f hf.continuous]
  funext x
  rw [average, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => (hf.differentiable (by norm_num) y).hasDerivAt)
    ((hf.continuous_deriv (by norm_num)).intervalIntegrable _ _)]

theorem deriv_contDiff_one (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) :=
  (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) f from hf)).2.2

theorem second_average (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (e : ℝ) :
    deriv (deriv (average f e)) = average (deriv (deriv f)) e := by
  rw [deriv_average_eq_average_deriv f (hf.of_le (by norm_num))]
  exact deriv_average_eq_average_deriv (deriv f) (deriv_contDiff_one f hf) e

theorem third_average (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (e : ℝ) :
    deriv (deriv (deriv (average f e))) =
      fun x => (deriv (deriv f) (x+e)-deriv (deriv f) x)/e := by
  rw [second_average f hf]
  apply average_deriv
  exact (deriv_contDiff_one f hf).continuous_deriv (by norm_num)

theorem average_norm_le (f : ℝ → ℝ) {e : ℝ} (he : 0 < e) (M : ℝ)
    (hM : ∀ x, ‖f x‖ ≤ M) (x : ℝ) : ‖average f e x‖ ≤ M := by
  rw [average, norm_div, Real.norm_eq_abs e, abs_of_pos he]
  apply (div_le_iff₀ he).mpr
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := x) (b := x+e) (fun y _ => hM y)
  simpa only [add_sub_cancel_left, abs_of_pos he] using h

theorem average_third_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) {e : ℝ} (he : 0 < e)
    (M : ℝ) (hM : ∀ x, ‖deriv (deriv f) x‖ ≤ M) (x : ℝ) :
    ‖deriv (deriv (deriv (average f e))) x‖ ≤ 2*M/e := by
  rw [third_average f hf, norm_div, Real.norm_eq_abs e, abs_of_pos he]
  gcongr
  exact (norm_sub_le _ _).trans (by linarith [hM (x+e), hM x])

theorem average_tendsto (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    Tendsto (fun e => average f e x) (𝓝[>] 0) (𝓝 (f x)) := by
  have h := (primitive_hasDerivAt hf 0 x).tendsto_slope_zero_right
  simpa only [average_eq_primitive f hf, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

theorem average_deriv_tendsto (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (x : ℝ) :
    Tendsto (fun e => deriv (average f e) x) (𝓝[>] 0) (𝓝 (deriv f x)) := by
  simp_rw [deriv_average_eq_average_deriv f hf]
  exact average_tendsto _ (hf.continuous_deriv (by norm_num)) x

theorem average_second_tendsto (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : ℝ) :
    Tendsto (fun e => deriv (deriv (average f e)) x) (𝓝[>] 0)
      (𝓝 (deriv (deriv f) x)) := by
  simp_rw [second_average f hf]
  exact average_tendsto _ ((deriv_contDiff_one f hf).continuous_deriv (by norm_num)) x

theorem average_error_le (f : ℝ → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {e : ℝ} (he : 0 < e) (x : ℝ) : ‖average f e x - f x‖ ≤ K * e := by
  have hi : average f e x - f x = (∫ y in x..(x+e), f y-f x)/e := by
    rw [intervalIntegral.integral_sub (hf.continuous.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [add_sub_cancel_left, smul_eq_mul, average]
    field_simp
  rw [hi, norm_div, Real.norm_eq_abs e, abs_of_pos he]
  apply (div_le_iff₀ he).mpr
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := (K:ℝ)*e) (a := x) (b := x+e) (f := fun y => f y-f x) ?_).trans_eq
    (by simp [abs_of_pos he])
  intro y hy
  have hy' : x < y ∧ y ≤ x+e := by simpa only [uIoc_of_le (by linarith : x ≤ x+e), mem_Ioc] using hy
  calc
    ‖f y-f x‖ ≤ K * ‖y-x‖ := hf.norm_sub_le y x
    _ ≤ K * e := by
      rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hy'.1)]
      gcongr
      linarith [hy'.2]

def width (n : ℕ) : ℝ := 1 / (n+1)

theorem width_pos (n : ℕ) : 0 < width n := by unfold width; positivity

theorem width_tendsto : Tendsto width atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall width_pos⟩
  exact tendsto_const_nhds.div_atTop
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem approximation_C3 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (n : ℕ) :
    ContDiff ℝ 3 (average f (width n)) := average_contDiff_succ f hf _

theorem approximation_first_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (M : ℝ)
    (hM : ∀ x, ‖deriv f x‖ ≤ M) (n : ℕ) (x : ℝ) :
    ‖deriv (average f (width n)) x‖ ≤ M := by
  rw [deriv_average_eq_average_deriv f (hf.of_le (by norm_num))]
  exact average_norm_le _ (width_pos n) M hM x

theorem approximation_second_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (M : ℝ)
    (hM : ∀ x, ‖deriv (deriv f) x‖ ≤ M) (n : ℕ) (x : ℝ) :
    ‖deriv (deriv (average f (width n))) x‖ ≤ M := by
  rw [second_average f hf]
  exact average_norm_le _ (width_pos n) M hM x

end OperatorDerivativeRewrite.Foundation.RealSteklovApprox






