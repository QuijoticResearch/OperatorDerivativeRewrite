import Foundation.PureOrderAppellParameter
import Foundation.PureOrderTaylorInnovations

/-! Canonical centered Taylor increments for the actual backward-heat Appell
martingale. The positive-order expansion has no omitted drift or higher powers. -/
noncomputable section
open Polynomial
open scoped BigOperators
namespace OperatorDerivativeRewrite.Foundation.PureOrderAppellCenteredStep
open PureOrderAppellCalculus PureOrderAppellTransition PureOrderAppellExpansion
open PureOrderAppellPairing PureOrderAppellParameter PureOrderTaylorInnovations
open PseudoPolynomialStein

theorem taylor_eq_shift (x : ℝ) (P : Polynomial ℝ) : taylor x P = shift x P := by
  apply Polynomial.funext
  intro z
  simp only [taylor_eval, shift, eval_comp, eval_add, eval_X, eval_C]

theorem centered_step (p : ℕ) (hp : 1 < p) (a b : ℝ) (N : ℕ) (x z : ℝ) :
    (appell p (a+b) N).eval (x+z) - (appell p b N).eval x =
      ∑ r ∈ Finset.range N,
        (((N.descFactorial (r+1):ℝ)/((r+1).factorial:ℝ))*
          (appell p (a+b) (N-(r+1))).eval x)*(z^(r+1)-moment p a (r+1)) := by
  have h := centered_taylor_eval p a x z (appell p (a+b) N)
  rw [taylor_eq_shift, appell_transition p hp,
    (appell_monic_degree p (a+b) N).natDegree_eq, Finset.sum_range_succ'] at h
  simp only [Function.iterate_zero_apply, Nat.factorial_zero, Nat.cast_one, div_one,
    pow_zero, moment_zero, sub_self, mul_zero, add_zero] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro r _
  rw [appell_iterate, eval_smul]
  simp only [smul_eq_mul]
  ring

theorem initial_mean (p : ℕ) (hp : 1 < p) (a : ℝ) (N : ℕ) :
    (appell p (-a) N).eval 0 = moment p a N := by
  have h := appell_transition p hp a (-a) N 0
  simp only [add_neg_cancel, zero_parameter, shift, C_0, add_zero, comp_X,
    expectation_X_pow] at h
  exact h.symm

end OperatorDerivativeRewrite.Foundation.PureOrderAppellCenteredStep
