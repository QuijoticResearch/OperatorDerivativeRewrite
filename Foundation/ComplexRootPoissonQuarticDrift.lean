import Foundation.ComplexRootPoissonPolynomialDomain
import Foundation.PoissonCountMoments
import Foundation.ComplexRootPoissonSemigroup

/-! Actual shifted quartic expectations of finite walks and compound-root probability laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonQuarticDrift
open ComplexFourthRootNoise ComplexFourthRootWalk ComplexRootOneStepCalculus
open ComplexRootPoissonPolynomialDomain ComplexRootPoissonSemigroup

theorem walk_shifted_quartic (n : ℕ) (a : ℝ) (z : ℂ) :
    (∫ ω, (z+terminal n a ω)^4 ∂ComplexFourthRootWalk.probability n) =
      z^4-4*(n : ℂ)*(a : ℂ)^4 := by
  induction n generalizing z with
  | zero => simp [terminal]
  | succ n ih =>
    rw [walk_successor_integral n a (fun y : ℂ => y^4) z]
    simp_rw [ih]
    rw [integral_sub Integrable.of_finite (integrable_const _), shifted_fourth]
    simp only [integral_const, probReal_univ, one_smul]
    push_cast
    ring

theorem complex_count_integrable (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℂ)) (poissonMeasure r) := by
  have he := Complex.ofRealCLM.integrable_comp (PoissonCountMoments.count_integrable r)
  change Integrable (fun n : ℕ => ((n : ℝ) : ℂ)) (poissonMeasure r) at he
  simpa only [Complex.ofReal_natCast] using he

theorem complex_count_integral (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℂ) ∂poissonMeasure r) = (r : ℂ) := by
  simpa only [Complex.ofReal_natCast, PoissonCountMoments.count_integral] using
    (integral_complex_ofReal (μ := poissonMeasure r) (f := fun n : ℕ => (n : ℝ)))

theorem shifted_quartic_integral (r : ℝ≥0) (a : ℝ) (z : ℂ) :
    (∫ y : ℂ, (z+y)^4 ∂ComplexRootPoissonLaw.law r a) =
      z^4-4*(r : ℂ)*(a : ℂ)^4 := by
  rw [shifted_power_mixture r a z 4]
  simp_rw [walk_shifted_quartic]
  rw [integral_sub (integrable_const _)
    (((complex_count_integrable r).const_mul 4).mul_const ((a : ℂ)^4)),
    integral_mul_const, integral_const_mul, complex_count_integral]
  simp

theorem quartic_integral (r : ℝ≥0) (a : ℝ) :
    (∫ y : ℂ, y^4 ∂ComplexRootPoissonLaw.law r a) = -4*(r : ℂ)*(a : ℂ)^4 := by
  simpa using shifted_quartic_integral r a 0

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonQuarticDrift
