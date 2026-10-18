import Foundation.PureOrderAppellCalculus
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-! Uniform pure-order finite Appell bases and derivative-expectation coordinates. -/
noncomputable section
open Polynomial
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.PureOrderAppellExpansion
open PureOrderAppellCalculus PseudoPolynomialStein

theorem appell_monic_degree (p : ℕ) (a : ℝ) (n : ℕ) : IsMonicOfDegree (appell p a n) n := by
  induction n with
  | zero => simp [appell]
  | succ n ih =>
    change IsMonicOfDegree (X * appell p a n - ((p:ℝ)*a) • derivative^[p-1] (appell p a n)) (n+1)
    have hhead : IsMonicOfDegree (X * appell p a n) (n+1) := by
      simpa only [Nat.add_comm] using (isMonicOfDegree_X ℝ).mul ih
    apply hhead.sub
    have h := (natDegree_smul_le ((p:ℝ)*a) (derivative^[p-1] (appell p a n))).trans
      (natDegree_iterate_derivative (appell p a n) (p-1))
    rw [ih.natDegree_eq] at h
    omega

def sequence (p : ℕ) (a : ℝ) : Polynomial.Sequence ℝ where
  elems' := appell p a
  degree_eq' n := (degree_eq_natDegree (appell_monic_degree p a n).monic.ne_zero).trans
    (congrArg (fun k : ℕ => (k : WithBot ℕ)) (appell_monic_degree p a n).natDegree_eq)

def basis (p : ℕ) (a : ℝ) : Module.Basis ℕ ℝ (Polynomial ℝ) :=
  (sequence p a).basis (fun n => by
    change IsUnit (appell p a n).leadingCoeff
    rw [(appell_monic_degree p a n).leadingCoeff_eq]
    exact isUnit_one)

theorem basis_apply (p : ℕ) (a : ℝ) (n : ℕ) : basis p a n = appell p a n := by
  exact Polynomial.Sequence.basis_eq_self _ _ _

theorem expectation_iterate_appell (p : ℕ) (a : ℝ) (k n : ℕ) :
    expectation p a (derivative^[k] (appell p a n)) =
      if n=k then (n.factorial : ℝ) else 0 := by
  induction k generalizing n with
  | zero =>
    cases n with
    | zero => simp [appell, PseudoFiniteGramObstruction.expectation_one]
    | succ n => simpa using appell_mean_zero p a n
  | succ k ih =>
    cases n with
    | zero => simp [appell, iterate_derivative_one (Nat.zero_lt_succ k)]
    | succ n =>
      rw [Function.iterate_succ_apply, appell_derivative, iterate_derivative_smul,
        map_smul, ih]
      by_cases h : n=k
      · subst n
        simp [smul_eq_mul, Nat.factorial_succ]
      · simp [h, smul_eq_mul]

def coordinate (p : ℕ) (a : ℝ) (n : ℕ) : Polynomial ℝ →ₗ[ℝ] ℝ :=
  ((n.factorial : ℝ)⁻¹) • ((expectation p a).comp
    ((derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)^n))

theorem coordinate_apply (p : ℕ) (a : ℝ) (n : ℕ) (P : Polynomial ℝ) :
    coordinate p a n P = expectation p a (derivative^[n] P) / (n.factorial : ℝ) := by
  simp [coordinate, Module.End.pow_apply, div_eq_mul_inv, mul_comm]

theorem coordinate_appell (p : ℕ) (a : ℝ) (n k : ℕ) :
    coordinate p a n (appell p a k) = if k=n then 1 else 0 := by
  rw [coordinate_apply, expectation_iterate_appell]
  by_cases h : k=n
  · subst k
    simp [Nat.factorial_ne_zero]
  · simp [h]

theorem coordinate_eq_basis_coord (p : ℕ) (a : ℝ) (n : ℕ) :
    coordinate p a n = (basis p a).coord n := by
  apply (basis p a).ext
  intro k
  rw [basis_apply, coordinate_appell]
  change (if k=n then (1:ℝ) else 0) = (basis p a).repr (appell p a k) n
  rw [← basis_apply, Module.Basis.repr_self_apply]

theorem repr_formula (p : ℕ) (a : ℝ) (P : Polynomial ℝ) (n : ℕ) :
    (basis p a).repr P n = expectation p a (derivative^[n] P) / (n.factorial : ℝ) := by
  rw [← Module.Basis.coord_apply, ← coordinate_eq_basis_coord, coordinate_apply]

theorem expansion (p : ℕ) (a : ℝ) (P : Polynomial ℝ) :
    ∑ n ∈ ((basis p a).repr P).support,
      (expectation p a (derivative^[n] P) / (n.factorial : ℝ)) • appell p a n = P := by
  have h := (basis p a).linearCombination_repr P
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, basis_apply, repr_formula]
    using h

end OperatorDerivativeRewrite.Foundation.PureOrderAppellExpansion
