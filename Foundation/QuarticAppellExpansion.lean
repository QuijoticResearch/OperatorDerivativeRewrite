import Foundation.QuarticAppellCalculus
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-! Global finite Appell expansion with derivative-expectation coordinate functionals. -/
noncomputable section
open Polynomial
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.QuarticAppellExpansion
open QuarticAppellCalculus PseudoPolynomialStein

theorem appell_monic_degree (a : ℝ) (n : ℕ) : IsMonicOfDegree (appell a n) n := by
  induction n with
  | zero => simp [appell]
  | succ n ih =>
    change IsMonicOfDegree (X * appell a n - (4*a) • derivative^[3] (appell a n)) (n+1)
    have hhead : IsMonicOfDegree (X * appell a n) (n+1) := by
      simpa only [Nat.add_comm] using (isMonicOfDegree_X ℝ).mul ih
    apply hhead.sub
    have h := (natDegree_smul_le (4*a) (derivative^[3] (appell a n))).trans
      (natDegree_iterate_derivative (appell a n) 3)
    rw [ih.natDegree_eq] at h
    omega

def sequence (a : ℝ) : Polynomial.Sequence ℝ where
  elems' := appell a
  degree_eq' n := (degree_eq_natDegree (appell_monic_degree a n).monic.ne_zero).trans
    (congrArg (fun k : ℕ => (k : WithBot ℕ)) (appell_monic_degree a n).natDegree_eq)

def basis (a : ℝ) : Module.Basis ℕ ℝ (Polynomial ℝ) :=
  (sequence a).basis (fun n => by
    change IsUnit (appell a n).leadingCoeff
    rw [(appell_monic_degree a n).leadingCoeff_eq]
    exact isUnit_one)

theorem basis_apply (a : ℝ) (n : ℕ) : basis a n = appell a n := by
  exact Polynomial.Sequence.basis_eq_self _ _ _

theorem expectation_iterate_appell (a : ℝ) (k n : ℕ) :
    expectation 4 a (derivative^[k] (appell a n)) =
      if n=k then (n.factorial : ℝ) else 0 := by
  induction k generalizing n with
  | zero =>
    cases n with
    | zero => simp [appell, PseudoFiniteGramObstruction.expectation_one]
    | succ n => simpa using appell_mean_zero a n
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

def coordinate (a : ℝ) (n : ℕ) : Polynomial ℝ →ₗ[ℝ] ℝ :=
  ((n.factorial : ℝ)⁻¹) • ((expectation 4 a).comp
    ((derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)^n))

theorem coordinate_apply (a : ℝ) (n : ℕ) (P : Polynomial ℝ) :
    coordinate a n P = expectation 4 a (derivative^[n] P) / (n.factorial : ℝ) := by
  simp [coordinate, Module.End.pow_apply, div_eq_mul_inv, mul_comm]

theorem coordinate_appell (a : ℝ) (n k : ℕ) :
    coordinate a n (appell a k) = if k=n then 1 else 0 := by
  rw [coordinate_apply, expectation_iterate_appell]
  by_cases h : k=n
  · subst k
    simp [Nat.factorial_ne_zero]
  · simp [h]

theorem coordinate_eq_basis_coord (a : ℝ) (n : ℕ) :
    coordinate a n = (basis a).coord n := by
  apply (basis a).ext
  intro k
  rw [basis_apply, coordinate_appell]
  change (if k=n then (1:ℝ) else 0) = (basis a).repr (appell a k) n
  rw [← basis_apply, Module.Basis.repr_self_apply]

theorem repr_formula (a : ℝ) (P : Polynomial ℝ) (n : ℕ) :
    (basis a).repr P n = expectation 4 a (derivative^[n] P) / (n.factorial : ℝ) := by
  rw [← Module.Basis.coord_apply, ← coordinate_eq_basis_coord, coordinate_apply]

theorem expansion (a : ℝ) (P : Polynomial ℝ) :
    ∑ n ∈ ((basis a).repr P).support,
      (expectation 4 a (derivative^[n] P) / (n.factorial : ℝ)) • appell a n = P := by
  have h := (basis a).linearCombination_repr P
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, basis_apply, repr_formula]
    using h

theorem actual_coordinate (t : ℝ≥0) (ht : 0 < t) (P : Polynomial ℝ) (n : ℕ) :
    (basis (-(t:ℝ))).repr P n =
      HigherHeatPolynomialRealization.kernelExpectation 2 (by norm_num) t ht
        (derivative^[n] P) / (n.factorial : ℝ) := by
  rw [repr_formula, HigherHeatPolynomialRealization.kernelExpectation_eq_moments]
  norm_num

end OperatorDerivativeRewrite.Foundation.QuarticAppellExpansion
