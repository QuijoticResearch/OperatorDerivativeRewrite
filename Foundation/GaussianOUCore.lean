import Foundation.GaussianCore

/-! Actual one-dimensional Gaussian OU polynomial calculus. The generator is
p''-x p'; Gamma and Gamma2 are computed from their defining generator recursion.
This is not a fractional-time generator or a closed-generator domain theorem. -/
noncomputable section
open MeasureTheory Polynomial
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianOUCore
open GaussianCore

def generator (p : ℝ[X]) : ℝ[X] := p.derivative.derivative - X * p.derivative

def gamma (p q : ℝ[X]) : ℝ[X] :=
  C (1/2:ℝ) * (generator (p*q) - p*generator q - q*generator p)

def gammaTwo (p q : ℝ[X]) : ℝ[X] :=
  C (1/2:ℝ) * (generator (gamma p q) - gamma p (generator q) - gamma q (generator p))

theorem generator_actual_derivatives (p : ℝ[X]) (x : ℝ) :
    (generator p).eval x = deriv (deriv (fun y => p.eval y)) x - x * deriv (fun y => p.eval y) x := by
  have he : deriv (fun y => p.eval y) = fun y => p.derivative.eval y := funext fun y => p.deriv
  rw [he, p.derivative.deriv]
  simp [generator]

theorem gamma_formula (p q : ℝ[X]) : gamma p q = p.derivative*q.derivative := by
  simp only [gamma, generator, derivative_mul, map_add, mul_add, add_mul]
  have hc : C (1/2:ℝ) * (2:ℝ[X]) = 1 := by
    have hh := congrArg (Polynomial.C : ℝ → ℝ[X]) (show (1/2:ℝ)*2=1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using hh
  linear_combination (p.derivative*q.derivative) * hc

theorem gammaTwo_formula (p q : ℝ[X]) :
    gammaTwo p q = p.derivative*q.derivative + p.derivative.derivative*q.derivative.derivative := by
  simp only [gammaTwo, gamma_formula, generator, derivative_mul, map_add, map_sub,
    derivative_X, one_mul]
  have hc : C (1/2:ℝ) * (2:ℝ[X]) = 1 := by
    have hh := congrArg (Polynomial.C : ℝ → ℝ[X]) (show (1/2:ℝ)*2=1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using hh
  linear_combination (p.derivative*q.derivative + p.derivative.derivative*q.derivative.derivative) * hc

theorem gamma_actual_derivatives (p q : ℝ[X]) (x : ℝ) :
    (gamma p q).eval x = deriv (fun y => p.eval y) x * deriv (fun y => q.eval y) x := by
  rw [gamma_formula, eval_mul, p.deriv, q.deriv]

theorem gamma_nonneg (p : ℝ[X]) (x : ℝ) : 0 ≤ (gamma p p).eval x := by
  rw [gamma_formula, eval_mul]
  exact mul_self_nonneg _

theorem gaussian_curvature_one (p : ℝ[X]) (x : ℝ) :
    (gamma p p).eval x ≤ (gammaTwo p p).eval x := by
  rw [gammaTwo_formula, gamma_formula, eval_add, eval_mul, eval_mul]
  linarith [mul_self_nonneg (p.derivative.derivative.eval x)]

theorem generator_integrable (p : ℝ[X]) : Integrable (fun x => (generator p).eval x) γ :=
  (polynomial_memLp _ 1 (by simp)).integrable (by simp)

theorem gamma_integrable (p q : ℝ[X]) : Integrable (fun x => (gamma p q).eval x) γ :=
  (polynomial_memLp _ 1 (by simp)).integrable (by simp)

theorem gammaTwo_integrable (p q : ℝ[X]) : Integrable (fun x => (gammaTwo p q).eval x) γ :=
  (polynomial_memLp _ 1 (by simp)).integrable (by simp)

theorem gaussian_generator_pairing (p q : ℝ[X]) :
    ∫ x, (gamma p q).eval x ∂γ = -∫ x, p.eval x * (generator q).eval x ∂γ := by
  have hi := polynomial_integration_by_parts p q.derivative
  have he : divergencePolynomial q.derivative = - generator q := by
    simp [divergencePolynomial, generator]
  rw [he] at hi
  simp only [eval_neg, mul_neg, integral_neg] at hi
  simpa only [gamma_formula, eval_mul] using hi

theorem gaussian_generator_symmetric (p q : ℝ[X]) :
    ∫ x, p.eval x * (generator q).eval x ∂γ =
      ∫ x, q.eval x * (generator p).eval x ∂γ := by
  have hp := gaussian_generator_pairing p q
  have hq := gaussian_generator_pairing q p
  have he : gamma p q = gamma q p := by simp [gamma_formula, mul_comm]
  rw [he] at hp
  linarith

theorem gaussian_generator_energy (p : ℝ[X]) :
    -∫ x, p.eval x * (generator p).eval x ∂γ = ∫ x, (p.derivative.eval x)^2 ∂γ := by
  rw [← gaussian_generator_pairing, gamma_formula]
  simp only [eval_mul, pow_two]

end OperatorDerivativeRewrite.Foundation.GaussianOUCore
