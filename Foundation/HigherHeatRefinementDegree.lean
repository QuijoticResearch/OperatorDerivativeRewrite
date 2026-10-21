import Foundation.HigherHeatRefinedPredictableJets

/-! One fixed polynomial degree bound along every actual block refinement. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.HigherHeatRefinementDegree
open HigherHeatPolynomialCylinders HigherHeatPolynomialRefinement HigherHeatRefinedPredictableJets

theorem linear_substitution_degree {ι κ : Type*} (v : ι → MvPolynomial κ ℝ)
    (hv : ∀ i, (v i).totalDegree ≤ 1) (P : MvPolynomial ι ℝ) :
    (MvPolynomial.aeval v P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.aeval_monomial, Finsupp.prod]
  change (MvPolynomial.C (P.coeff d) * ∏ i ∈ d.support, v i ^ d i).totalDegree ≤ _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  apply (Finset.sum_le_sum (fun i _ =>
    (MvPolynomial.totalDegree_pow (v i) (d i)).trans
      ((Nat.mul_le_mul_left (d i) (hv i)).trans_eq (Nat.mul_one (d i))))).trans
  exact MvPolynomial.le_totalDegree hd

theorem block_pullback_degree {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → κ) (P : MvPolynomial κ ℝ) : (pullback p P).totalDegree ≤ P.totalDegree := by
  classical
  apply linear_substitution_degree
  intro i
  exact MvPolynomial.totalDegree_finsetSum_le (fun j _ => by simp)

theorem step_degree (n : ℕ) (P : Test n) : (step n P).totalDegree ≤ P.totalDegree :=
  block_pullback_degree _ P

theorem transfer_degree (b n : ℕ) (hn : b ≤ n) (P : Test b) :
    (transfer b n hn P).totalDegree ≤ P.totalDegree := by
  induction n, hn using Nat.le_induction with
  | base => rw [transfer_self]
  | succ n hn ih =>
    rw [transfer_succ b n hn]
    exact (step_degree n _).trans ih

theorem refined_input_degree (b : ℕ) (P : Test b) (n : ℕ) :
    (refinedInput b P n).totalDegree ≤ P.totalDegree := by
  by_cases hn : b ≤ n
  · rw [refinedInput, dite_eq_left hn]
    exact transfer_degree b n hn P
  · rw [refinedInput, dite_eq_right hn, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _

end OperatorDerivativeRewrite.Foundation.HigherHeatRefinementDegree
