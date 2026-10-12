import Foundation.GaussianPolynomialHeat
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Actual real derivatives of space-time polynomial evaluation, and compatibility
with Mathlib's univariate Polynomial.derivative. -/
noncomputable section
open MvPolynomial
namespace OperatorDerivativeRewrite.Foundation.GaussianPolynomialDifferentiation
open GaussianPolynomialHeat

theorem eval_hasDerivAt_space (p : SpaceTimePolynomial) (t x : ℝ) :
    HasDerivAt (fun y => eval ![t, y] p) (eval ![t, x] (pderiv 1 p)) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const x c
  | add p q hp hq => convert hp.add hq using 1 <;> (try funext y) <;> simp
  | mul_X p i hp =>
    fin_cases i
    · convert hp.mul_const t using 1 <;> (try funext y) <;> simp <;> ring
    · convert hp.mul (hasDerivAt_id x) using 1 <;> (try funext y) <;> simp <;> ring

theorem eval_hasDerivAt_time (p : SpaceTimePolynomial) (t x : ℝ) :
    HasDerivAt (fun s => eval ![s, x] p) (eval ![t, x] (pderiv 0 p)) t := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const t c
  | add p q hp hq => convert hp.add hq using 1 <;> (try funext y) <;> simp
  | mul_X p i hp =>
    fin_cases i
    · convert hp.mul (hasDerivAt_id t) using 1 <;> (try funext y) <;> simp <;> ring
    · convert hp.mul_const x using 1 <;> (try funext y) <;> simp <;> ring

theorem heat_eval_actual (p : SpaceTimePolynomial) (t x : ℝ) :
    eval ![t, x] (heat p) = deriv (fun s => eval ![s, x] p) t +
      (1 / 2 : ℝ) * deriv (fun y => deriv (fun z => eval ![t, z] p) y) x := by
  have hs : (fun y => deriv (fun z => eval ![t, z] p) y) =
      fun y => eval ![t, y] (pderiv 1 p) := funext fun y => (eval_hasDerivAt_space p t y).deriv
  rw [hs, (eval_hasDerivAt_time p t x).deriv, (eval_hasDerivAt_space (pderiv 1 p) t x).deriv]
  simp [heat_apply]

def spatialPolynomial (p : Polynomial ℝ) : SpaceTimePolynomial := p.toMvPolynomial 1

theorem spatialPolynomial_eval (p : Polynomial ℝ) (t x : ℝ) :
    eval ![t, x] (spatialPolynomial p) = p.eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [spatialPolynomial] using congrArg₂ (· + ·) hp hq
  | monomial n c => simp [spatialPolynomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]

theorem spatialPolynomial_spatial (p : Polynomial ℝ) :
    pderiv 1 (spatialPolynomial p) = spatialPolynomial p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [spatialPolynomial] using congrArg₂ (· + ·) hp hq
  | monomial n c =>
    simp [spatialPolynomial, ← Polynomial.C_mul_X_pow_eq_monomial, pderiv_pow,
      Polynomial.derivative_monomial, Polynomial.derivative_X_pow, map_mul, map_pow]

theorem spatialPolynomial_time (p : Polynomial ℝ) : pderiv 0 (spatialPolynomial p) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [spatialPolynomial] using congrArg₂ (· + ·) hp hq
  | monomial n c => simp [spatialPolynomial, ← Polynomial.C_mul_X_pow_eq_monomial, pderiv_pow]

theorem spatialPolynomial_heat (p : Polynomial ℝ) :
    heat (spatialPolynomial p) = (1 / 2 : ℝ) • spatialPolynomial p.derivative.derivative := by
  rw [heat_apply, spatialPolynomial_time, zero_add, spatialPolynomial_spatial,
    spatialPolynomial_spatial]

end OperatorDerivativeRewrite.Foundation.GaussianPolynomialDifferentiation
