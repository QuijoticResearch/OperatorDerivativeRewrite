import Foundation.StickyBoundaryGeneratorCore
import Foundation.SmoothAbsoluteApproximation
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Group.Bounded

/-! A concrete nonzero C0 boundary test for the actual sticky candidate.
Its smooth base has bounded first and second derivatives. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology ZeroAtInfty
namespace OperatorDerivativeRewrite.Foundation.StickyVanishingBoundaryTest
open InfiniteGaussian BrownianMassRandomTimeChange SmoothAbsoluteApproximation
open StickyC2MartingaleProblem StickyBoundaryGeneratorCore
set_option backward.isDefEq.respectTransparency false

def a (κ : ℝ≥0) : ℝ≥0 := 1+κ/4
def b (κ : ℝ≥0) : ℝ≥0 := 1+κ/2
def base (κ : ℝ≥0) (x : ℝ) : ℝ := (a κ : ℝ)*radius 1 x-(b κ : ℝ)*radius 2 x
def test (κ : ℝ≥0) : ℝ → ℝ := boundaryTest (base κ) κ

theorem base_smooth (κ : ℝ≥0) : ContDiff ℝ 2 (base κ) :=
  (contDiff_const.mul (radius_smooth (by norm_num : (0 : ℝ) < 1) 2)).sub
    (contDiff_const.mul (radius_smooth (by norm_num : (0 : ℝ) < 2) 2))

theorem base_deriv (κ : ℝ≥0) : deriv (base κ) =
    fun x => (a κ : ℝ)*SmoothAbsoluteApproximation.slope 1 x-(b κ : ℝ)*SmoothAbsoluteApproximation.slope 2 x := by
  funext x
  exact (((radius_hasDerivAt (by norm_num : (0 : ℝ) < 1) x).const_mul (a κ : ℝ)).sub
    ((radius_hasDerivAt (by norm_num : (0 : ℝ) < 2) x).const_mul (b κ : ℝ))).deriv

theorem base_second_deriv (κ : ℝ≥0) : deriv (deriv (base κ)) =
    fun x => (a κ : ℝ)*curvature 1 x-(b κ : ℝ)*curvature 2 x := by
  rw [base_deriv]
  funext x
  exact (((slope_hasDerivAt (by norm_num : (0 : ℝ) < 1) x).const_mul (a κ : ℝ)).sub
    ((slope_hasDerivAt (by norm_num : (0 : ℝ) < 2) x).const_mul (b κ : ℝ))).deriv

theorem base_first_bound (κ : ℝ≥0) (x : ℝ) : ‖deriv (base κ) x‖₊ ≤ a κ+b κ := by
  change ‖deriv (base κ) x‖ ≤ ((a κ+b κ : ℝ≥0) : ℝ)
  rw [base_deriv]
  calc
    _ ≤ ‖(a κ : ℝ)*SmoothAbsoluteApproximation.slope 1 x‖+
        ‖(b κ : ℝ)*SmoothAbsoluteApproximation.slope 2 x‖ := norm_sub_le _ _
    _ = (a κ : ℝ)*‖SmoothAbsoluteApproximation.slope 1 x‖+
        (b κ : ℝ)*‖SmoothAbsoluteApproximation.slope 2 x‖ := by simp [norm_mul]
    _ ≤ (a κ : ℝ)*1+(b κ : ℝ)*1 := add_le_add
      (mul_le_mul_of_nonneg_left (slope_bound (by norm_num) x) (a κ).coe_nonneg)
      (mul_le_mul_of_nonneg_left (slope_bound (by norm_num) x) (b κ).coe_nonneg)
    _ = _ := by simp

theorem base_second_bound (κ : ℝ≥0) (x : ℝ) : ‖deriv (deriv (base κ)) x‖₊ ≤ a κ+b κ/2 := by
  change ‖deriv (deriv (base κ)) x‖ ≤ ((a κ+b κ/2 : ℝ≥0) : ℝ)
  rw [base_second_deriv]
  calc
    _ ≤ ‖(a κ : ℝ)*curvature 1 x‖+‖(b κ : ℝ)*curvature 2 x‖ := norm_sub_le _ _
    _ = (a κ : ℝ)*‖curvature 1 x‖+(b κ : ℝ)*‖curvature 2 x‖ := by simp [norm_mul]
    _ ≤ (a κ : ℝ)*1+(b κ : ℝ)*(1/2) := add_le_add
      (mul_le_mul_of_nonneg_left (by simpa using curvature_bound (by norm_num : (0 : ℝ) < 1) x)
        (a κ).coe_nonneg)
      (mul_le_mul_of_nonneg_left (by simpa using curvature_bound (by norm_num : (0 : ℝ) < 2) x)
        (b κ).coe_nonneg)
    _ = _ := by simp; ring

theorem base_second_zero (κ : ℝ≥0) : deriv (deriv (base κ)) 0 = 1/2 := by
  have hs : Real.sqrt (4 : ℝ) = 2 := by
    have h := Real.sqrt_sq_eq_abs (2 : ℝ)
    norm_num at h
    exact h
  rw [base_second_deriv]
  norm_num [curvature,radius,a,b,hs]
  ring

theorem coefficient_eq (κ : ℝ≥0) : coefficient (base κ) κ = (κ : ℝ)/4 := by
  rw [coefficient, base_second_zero]
  ring

theorem test_error_form (κ : ℝ≥0) (x : ℝ) : test κ x =
    (a κ : ℝ)*(radius 1 x-|x|)-(b κ : ℝ)*(radius 2 x-|x|) := by
  unfold test boundaryTest
  rw [coefficient_eq]
  unfold base a b
  push_cast
  ring

theorem radius_error_identity (e : ℝ) (he : 0 < e) (x : ℝ) :
    radius e x-|x| = e^2/(radius e x+|x|) := by
  have hp : 0 < radius e x+|x| := add_pos_of_pos_of_nonneg (radius_pos he x) (abs_nonneg x)
  apply (eq_div_iff (ne_of_gt hp)).mpr
  nlinarith [radius_sq he x, sq_abs x]

theorem radius_error_tendsto (e : ℝ) (he : 0 < e) :
    Tendsto (fun x => radius e x-|x|) (cocompact ℝ) (𝓝 0) := by
  have hd : Tendsto (fun x => radius e x+|x|) (cocompact ℝ) atTop := by
    apply tendsto_atTop.mpr
    intro R
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually (eventually_ge_atTop R)] with x hx
    have hx' : R ≤ |x| := by simpa only [Real.norm_eq_abs] using hx
    exact hx'.trans (le_add_of_nonneg_left (radius_pos he x).le)
  simp_rw [radius_error_identity e he]
  simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using hd.inv_tendsto_atTop.const_mul (e^2)

theorem test_tendsto (κ : ℝ≥0) : Tendsto (test κ) (cocompact ℝ) (𝓝 0) := by
  have h := ((radius_error_tendsto 1 (by norm_num)).const_mul (a κ : ℝ)).sub
    ((radius_error_tendsto 2 (by norm_num)).const_mul (b κ : ℝ))
  have he : test κ = fun x => (a κ : ℝ)*(radius 1 x-|x|)-(b κ : ℝ)*(radius 2 x-|x|) :=
    funext (test_error_form κ)
  rw [he]
  simpa only [mul_zero, sub_zero] using h

def testC0 (κ : ℝ≥0) : C₀(ℝ, ℝ) where
  toFun := test κ
  continuous_toFun := boundaryTest_continuous (base κ) (base_smooth κ) κ
  zero_at_infty' := test_tendsto κ

theorem test_zero (κ : ℝ≥0) : test κ 0 = -1-3*(κ : ℝ)/4 := by
  have hs : Real.sqrt (4 : ℝ) = 2 := by
    have h := Real.sqrt_sq_eq_abs (2 : ℝ)
    norm_num at h
    exact h
  rw [test_error_form]
  norm_num [radius,a,b,hs]
  ring

theorem test_nonzero (κ : ℝ≥0) : testC0 κ ≠ 0 := by
  intro h
  have he := congrArg (fun F : C₀(ℝ, ℝ) => F 0) h
  change test κ 0 = 0 at he
  rw [test_zero] at he
  nlinarith [κ.coe_nonneg]

theorem concrete_martingale (κ : ℝ≥0) :
    Martingale (fun t ω => testC0 κ (changedPath κ ω t)-testC0 κ 0-
      ∫ s in 0..(t : ℝ), candidateGenerator (base κ) (changedPath κ ω s.toNNReal))
      (augmentedPhysicalPast κ) gaussianProduct :=
  generator_martingale (base κ) (base_smooth κ) (a κ+b κ) (a κ+b κ/2)
    (base_first_bound κ) (base_second_bound κ) κ

end OperatorDerivativeRewrite.Foundation.StickyVanishingBoundaryTest
