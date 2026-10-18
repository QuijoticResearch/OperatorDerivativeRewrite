import Foundation.PseudoFiniteGramObstruction

/-! Pure-order Appell raising calculus, uniformly in the cumulant order. -/
noncomputable section
open Polynomial
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.PureOrderAppellCalculus
open PseudoPolynomialStein PseudoClarkOconeObstruction

def raise (p : ℕ) (a : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  X * P - ((p:ℝ)*a) • derivative^[p-1] P

theorem raise_mean_zero (p : ℕ) (a : ℝ) (P : Polynomial ℝ) :
    expectation p a (raise p a P) = 0 := by
  rw [raise, map_sub, map_smul, polynomial_stein]
  simp only [smul_eq_mul]
  norm_num

theorem derivative_raise (p : ℕ) (a : ℝ) (P : Polynomial ℝ) :
    derivative (raise p a P) = P + raise p a (derivative P) := by
  simp only [raise, map_sub, derivative_mul, derivative_X, one_mul,
    derivative_smul]
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  ring

theorem raise_smul (p : ℕ) (a c : ℝ) (P : Polynomial ℝ) :
    raise p a (c • P) = c • raise p a P := by
  simp only [raise, mul_smul_comm, iterate_derivative_smul, smul_sub, smul_smul]
  rw [mul_comm ((p:ℝ)*a) c]

def appell (p : ℕ) (a : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | n+1 => raise p a (appell p a n)

theorem appell_mean_zero (p : ℕ) (a : ℝ) (n : ℕ) :
    expectation p a (appell p a (n+1)) = 0 := raise_mean_zero p a _

theorem appell_derivative (p : ℕ) (a : ℝ) (n : ℕ) :
    derivative (appell p a (n+1)) = (n+1 : ℝ) • appell p a n := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_add, one_smul, appell]
    rw [derivative_raise]
    simp [raise]
  | succ n ih =>
    change derivative (raise p a (appell p a (n+1))) = _
    rw [derivative_raise, ih, raise_smul]
    change appell p a (n+1) + (n+1 : ℝ) • appell p a (n+1) = _
    push_cast
    module

end OperatorDerivativeRewrite.Foundation.PureOrderAppellCalculus
