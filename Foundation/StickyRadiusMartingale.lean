import Foundation.StickyBoundaryGeneratorCore
import Foundation.SmoothAbsoluteApproximation

/-! A concrete nontrivial boundary test for the actual sticky candidate.
This test has linear growth; it is not declared an element of a C0 generator domain. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.StickyRadiusMartingale
open InfiniteGaussian BrownianMassRandomTimeChange SmoothAbsoluteApproximation
open StickyC2MartingaleProblem StickyBoundaryGeneratorCore
set_option backward.isDefEq.respectTransparency false

def test (κ : ℝ≥0) (x : ℝ) : ℝ := radius 1 x+(κ : ℝ)/2*|x|
def generator (x : ℝ) : ℝ := (1/2 : ℝ)*curvature 1 x

theorem first_bound (x : ℝ) : ‖deriv (radius 1) x‖₊ ≤ (1 : ℝ≥0) := by
  change ‖deriv (radius 1) x‖ ≤ (1 : ℝ)
  rw [radius_deriv (by norm_num : (0 : ℝ) < 1)]
  exact slope_bound (by norm_num) x

theorem second_bound (x : ℝ) : ‖deriv (deriv (radius 1)) x‖₊ ≤ (1 : ℝ≥0) := by
  change ‖deriv (deriv (radius 1)) x‖ ≤ (1 : ℝ)
  rw [radius_second_deriv (by norm_num : (0 : ℝ) < 1)]
  simpa using curvature_bound (by norm_num : (0 : ℝ) < 1) x

theorem coefficient_eq (κ : ℝ≥0) : coefficient (radius 1) κ = (κ : ℝ)/2 := by
  rw [coefficient, radius_second_deriv (by norm_num : (0 : ℝ) < 1)]
  norm_num [curvature,radius]

theorem test_eq (κ : ℝ≥0) : test κ = boundaryTest (radius 1) κ := by
  funext x
  rw [boundaryTest, coefficient_eq]
  rfl

theorem generator_eq : generator = candidateGenerator (radius 1) := by
  funext x
  rw [candidateGenerator, radius_second_deriv (by norm_num : (0 : ℝ) < 1)]
  rfl

theorem test_zero (κ : ℝ≥0) : test κ 0 = 1 := by norm_num [test,radius]
theorem generator_zero : generator 0 = 1/2 := by norm_num [generator,curvature,radius]

theorem right_derivative (κ : ℝ≥0) : HasDerivWithinAt (test κ) ((κ : ℝ)/2) (Ici 0) 0 := by
  rw [test_eq]
  have h := StickyC2MartingaleProblem.right_derivative (radius 1)
    (radius_smooth (by norm_num : (0 : ℝ) < 1) 2) κ
  simpa [radius_deriv (by norm_num : (0 : ℝ) < 1), SmoothAbsoluteApproximation.slope, coefficient_eq, neg_div] using h

theorem left_derivative (κ : ℝ≥0) : HasDerivWithinAt (test κ) (-(κ : ℝ)/2) (Iic 0) 0 := by
  rw [test_eq]
  have h := StickyC2MartingaleProblem.left_derivative (radius 1)
    (radius_smooth (by norm_num : (0 : ℝ) < 1) 2) κ
  simpa [radius_deriv (by norm_num : (0 : ℝ) < 1), SmoothAbsoluteApproximation.slope, coefficient_eq, neg_div] using h

theorem concrete_martingale (κ : ℝ≥0) :
    Martingale (fun t ω => test κ (changedPath κ ω t)-1-
      ∫ s in 0..(t : ℝ), generator (changedPath κ ω s.toNNReal))
      (augmentedPhysicalPast κ) gaussianProduct := by
  have h := generator_martingale (radius 1)
    (radius_smooth (by norm_num : (0 : ℝ) < 1) 2) 1 1 first_bound second_bound κ
  have hz : boundaryTest (radius 1) κ 0 = 1 := by rw [← test_eq, test_zero]
  simpa only [← test_eq, ← generator_eq, hz] using h

end OperatorDerivativeRewrite.Foundation.StickyRadiusMartingale
