import Foundation.HigherHeatPredictableJetFields

/-! One input-degree bound for every native conditional Taylor coefficient,
independent of the evaluation point and cell. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPredictableJetDegree
open HigherHeatPolynomialCylinders PureOrderPolynomialConditioning HigherHeatDyadicConditioning
open HigherHeatPredictableJetBounds HigherHeatPredictableJetIdentity MultivariatePolynomialNilpotence

theorem conditioning_degree {ι : Type*} [Fintype ι] (p : ℕ) (a : ι → ℝ)
    (S : Finset ι) (P : MvPolynomial ι ℝ) : (conditioning p a S P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [conditioning_monomial]
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  apply (Finsupp.degree_mono (a := keep S d) (b := d) ?_).trans (MvPolynomial.le_totalDegree hd)
  intro i
  by_cases hi : i ∈ S <;> simp [keep_apply, hi]

theorem jet_zero_above_degree (n m : ℕ) (T : ℝ≥0) (j : Fin (size n))
    (q : ℕ) (P : Test n) (hq : P.totalDegree < q) : predictableJet n m T j q P = 0 := by
  have hd : (nextConditioned n m T j P).totalDegree ≤ P.totalDegree := conditioning_degree _ _ _ P
  rw [predictableJet, iterate_zero _ _ q (hd.trans_lt hq), map_zero, smul_zero]

theorem slice_degree (n m : ℕ) (T : ℝ≥0) (j : Fin (size n)) (P : Test n)
    (x : Fin (size n) → ℝ) : (slice n m T j P x).natDegree ≤ P.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro q hq
  rw [slice, ← predictable_jet_coefficient, jet_zero_above_degree n m T j q P hq, map_zero]

end OperatorDerivativeRewrite.Foundation.HigherHeatPredictableJetDegree
