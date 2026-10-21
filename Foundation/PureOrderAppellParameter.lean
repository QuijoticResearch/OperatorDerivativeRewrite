import Foundation.PureOrderAppellTransition

/-! Finite polynomial dependence of the actual Appell family on its cumulant
parameter. The outer variable is spatial; the inner variable is the parameter. -/
noncomputable section
open Polynomial
open scoped BigOperators
namespace OperatorDerivativeRewrite.Foundation.PureOrderAppellParameter
open PureOrderAppellCalculus

def parametric (p : ℕ) : ℕ → Polynomial (Polynomial ℝ)
  | 0 => 1
  | n+1 => X * parametric p n - C ((p:ℝ) • (X:Polynomial ℝ)) *
      derivative^[p-1] (parametric p n)

theorem specialization (p n : ℕ) (a : ℝ) :
    (parametric p n).map (Polynomial.evalRingHom a) = appell p a n := by
  induction n with
  | zero => simp [parametric, appell]
  | succ n ih =>
    simp only [parametric, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
      Polynomial.map_C, ← Polynomial.iterate_derivative_map, ih, appell, raise]
    simp [smul_eq_C_mul]

theorem coefficient (p n r : ℕ) (a : ℝ) :
    (appell p a n).coeff r = ((parametric p n).coeff r).eval a := by
  rw [← specialization, coeff_map]
  rfl

theorem expansion (p n : ℕ) (a : ℝ) :
    appell p a n = ∑ r ∈ (parametric p n).support,
      (((parametric p n).coeff r).eval a) • (X:Polynomial ℝ)^r := by
  rw [← specialization]
  conv_lhs => rw [← (parametric p n).sum_C_mul_X_pow_eq]
  simp only [Polynomial.sum, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, smul_eq_C_mul]
  rfl

theorem zero_parameter (p n : ℕ) : appell p 0 n = (X:Polynomial ℝ)^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [appell, raise, ih, pow_succ, mul_comm]

end OperatorDerivativeRewrite.Foundation.PureOrderAppellParameter
