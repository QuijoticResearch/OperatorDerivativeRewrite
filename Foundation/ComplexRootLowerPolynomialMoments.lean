import Foundation.ComplexRootPoissonQuarticDrift

/-! Exact lower holomorphic polynomial moments of the genuine compound-root law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexRootLowerPolynomialMoments
open ComplexFourthRootNoise ComplexFourthRootWalk ComplexRootPoissonSemigroup
open ComplexRootPoissonPolynomialDomain

theorem noise_shifted_square (a : ℝ) (z : ℂ) :
    (∫ k, (z+noise a k)^2 ∂ComplexFourthRootNoise.probability) = z^2 := by
  rw [integral_formula]
  norm_num [noise,root]
  ring_nf
  norm_num [Complex.I_sq]

theorem noise_shifted_cube (a : ℝ) (z : ℂ) :
    (∫ k, (z+noise a k)^3 ∂ComplexFourthRootNoise.probability) = z^3 := by
  rw [integral_formula]
  norm_num [noise,root]
  ring_nf
  norm_num [Complex.I_sq]

theorem walk_shifted_square (n : ℕ) (a : ℝ) (z : ℂ) :
    (∫ ω, (z+terminal n a ω)^2 ∂ComplexFourthRootWalk.probability n) = z^2 := by
  induction n generalizing z with
  | zero => simp [terminal]
  | succ n ih =>
    rw [walk_successor_integral n a (fun y : ℂ => y^2) z]
    simp_rw [ih]
    exact noise_shifted_square a z

theorem walk_shifted_cube (n : ℕ) (a : ℝ) (z : ℂ) :
    (∫ ω, (z+terminal n a ω)^3 ∂ComplexFourthRootWalk.probability n) = z^3 := by
  induction n generalizing z with
  | zero => simp [terminal]
  | succ n ih =>
    rw [walk_successor_integral n a (fun y : ℂ => y^3) z]
    simp_rw [ih]
    exact noise_shifted_cube a z

theorem shifted_square_integral (h : ℝ≥0) (a : ℝ) (z : ℂ) :
    (∫ y : ℂ, (z+y)^2 ∂ComplexRootPoissonLaw.law h a) = z^2 := by
  rw [shifted_power_mixture h a z 2]
  simp_rw [walk_shifted_square]
  simp

theorem shifted_cube_integral (h : ℝ≥0) (a : ℝ) (z : ℂ) :
    (∫ y : ℂ, (z+y)^3 ∂ComplexRootPoissonLaw.law h a) = z^3 := by
  rw [shifted_power_mixture h a z 3]
  simp_rw [walk_shifted_cube]
  simp

theorem square_integral (h : ℝ≥0) (a : ℝ) :
    (∫ y : ℂ, y^2 ∂ComplexRootPoissonLaw.law h a) = 0 := by
  simpa using shifted_square_integral h a 0

theorem cube_integral (h : ℝ≥0) (a : ℝ) :
    (∫ y : ℂ, y^3 ∂ComplexRootPoissonLaw.law h a) = 0 := by
  simpa using shifted_cube_integral h a 0

end OperatorDerivativeRewrite.Foundation.ComplexRootLowerPolynomialMoments
