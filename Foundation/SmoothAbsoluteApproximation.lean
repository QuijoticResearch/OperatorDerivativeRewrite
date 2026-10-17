import Foundation.GaussianC2Ito
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Explicit smooth convex approximations to absolute value. All derivative
fields below are identified with actual derivatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.SmoothAbsoluteApproximation

def radius (e x : ℝ) : ℝ := Real.sqrt (x ^ 2 + e ^ 2)
def slope (e x : ℝ) : ℝ := x / radius e x
def curvature (e x : ℝ) : ℝ := e ^ 2 / radius e x ^ 3

theorem radius_pos {e : ℝ} (he : 0 < e) (x : ℝ) : 0 < radius e x := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg x, sq_pos_of_pos he]

theorem radius_sq {e : ℝ} (he : 0 < e) (x : ℝ) :
    radius e x ^ 2 = x ^ 2 + e ^ 2 := by
  apply Real.sq_sqrt
  positivity

theorem radius_smooth {e : ℝ} (he : 0 < e) (n : WithTop ℕ∞) :
    ContDiff ℝ n (radius e) := by
  apply ContDiff.sqrt ((contDiff_id.pow 2).add contDiff_const)
  intro x
  have : 0 < x ^ 2 + e ^ 2 := by nlinarith [sq_nonneg x, sq_pos_of_pos he]
  exact ne_of_gt this

theorem radius_hasDerivAt {e : ℝ} (he : 0 < e) (x : ℝ) :
    HasDerivAt (radius e) (slope e x) x := by
  have hp : x ^ 2 + e ^ 2 ≠ 0 := by nlinarith [sq_nonneg x, sq_pos_of_pos he]
  have h := (((hasDerivAt_id x).pow 2).add_const (e ^ 2)).sqrt hp
  convert h using 1
  · rfl
  · unfold slope radius
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, mul_one]
    field_simp
    norm_num

theorem slope_hasDerivAt {e : ℝ} (he : 0 < e) (x : ℝ) :
    HasDerivAt (slope e) (curvature e x) x := by
  have h := (hasDerivAt_id x).div (radius_hasDerivAt he x) (ne_of_gt (radius_pos he x))
  convert h using 1
  · rfl
  · unfold curvature slope
    simp only [id_eq, one_mul]
    field_simp [ne_of_gt (radius_pos he x)]
    nlinarith [radius_sq he x]

theorem radius_deriv {e : ℝ} (he : 0 < e) : deriv (radius e) = slope e := by
  funext x
  exact (radius_hasDerivAt he x).deriv

theorem radius_second_deriv {e : ℝ} (he : 0 < e) :
    deriv (deriv (radius e)) = curvature e := by
  rw [radius_deriv he]
  funext x
  exact (slope_hasDerivAt he x).deriv

theorem abs_le_radius {e : ℝ} (_he : 0 < e) (x : ℝ) : |x| ≤ radius e x := by
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg e]

theorem parameter_le_radius {e : ℝ} (_he : 0 < e) (x : ℝ) : e ≤ radius e x := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg x]

theorem radius_le_abs_add {e : ℝ} (he : 0 < e) (x : ℝ) : radius e x ≤ |x| + e := by
  apply (Real.sqrt_le_left (by positivity : 0 ≤ |x| + e)).mpr
  nlinarith [sq_abs x, abs_nonneg x]

theorem uniform_error {e : ℝ} (he : 0 < e) (x : ℝ) : ‖radius e x - |x|‖ ≤ e := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (abs_le_radius he x))]
  linarith [radius_le_abs_add he x]

theorem slope_bound {e : ℝ} (he : 0 < e) (x : ℝ) : ‖slope e x‖ ≤ 1 := by
  rw [slope, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (radius_pos he x)]
  exact (div_le_one (radius_pos he x)).mpr (abs_le_radius he x)

theorem curvature_nonneg {e : ℝ} (he : 0 < e) (x : ℝ) : 0 ≤ curvature e x := by
  unfold curvature
  exact div_nonneg (sq_nonneg e) (pow_nonneg (radius_pos he x).le 3)

theorem curvature_bound {e : ℝ} (he : 0 < e) (x : ℝ) : ‖curvature e x‖ ≤ e⁻¹ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (curvature_nonneg he x), curvature,
    div_le_iff₀ (pow_pos (radius_pos he x) 3)]
  have h := mul_le_mul_of_nonneg_left (parameter_le_radius he x) (sq_nonneg (radius e x))
  have hs : e ^ 2 ≤ radius e x ^ 2 := by nlinarith [radius_sq he x, sq_nonneg x]
  have hp : e ^ 2 * e ≤ radius e x ^ 3 := by nlinarith
  calc
    e ^ 2 = e⁻¹ * (e ^ 2 * e) := by field_simp
    _ ≤ e⁻¹ * radius e x ^ 3 := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr he.le)

theorem functionLip {e : ℝ} (he : 0 < e) : LipschitzWith 1 (radius e) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (radius_hasDerivAt he x).differentiableAt)
  intro x
  rw [radius_deriv he]
  exact slope_bound he x

theorem slopeLip {e : ℝ} (he : 0 < e) :
    LipschitzWith ⟨e⁻¹, inv_nonneg.mpr he.le⟩ (slope e) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (slope_hasDerivAt he x).differentiableAt)
  intro x
  rw [(slope_hasDerivAt he x).deriv]
  exact curvature_bound he x

end OperatorDerivativeRewrite.Foundation.SmoothAbsoluteApproximation
