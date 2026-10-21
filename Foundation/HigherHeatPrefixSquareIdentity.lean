import Foundation.HigherHeatPrefixFields

/-! Exact signed affine integration identifies native squared prefixes. -/
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPrefixSquareIdentity
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement HigherHeatCompletedAffineSteps
open HigherHeatSecondChannelSteps HigherHeatPrefixFields HigherHeatQuadraticItoData
open MultivariateFactorialDomain MultivariateFactorialSubstitution

theorem coefficient_prefix (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (c : ℕ) (hc : c ≤ size n) (F : Test n) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (size n) => j.val < c),
      coefficientField n m hm T hT j F) =
      segment 0 ((c:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))
        (pairing m hm T hT (core (cylinderOf n F))) := by
  induction c with
  | zero => simp [HigherHeatPrefixFields.segment, HigherHeatWeakStepFields.step]
  | succ c ih =>
    have hc' : c < size n := by omega
    let k : Fin (size n) := ⟨c, hc'⟩
    have hs : Finset.univ.filter (fun j : Fin (size n) => j.val < c+1) =
        insert k (Finset.univ.filter (fun j : Fin (size n) => j.val < c)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      dsimp [k]
      omega
    have hk : k ∉ Finset.univ.filter (fun j : Fin (size n) => j.val < c) := by simp [k]
    rw [hs, Finset.sum_insert hk, ih (by omega)]
    have hd := (HigherHeatDyadicLaws.duration 1 n).coe_nonneg
    rw [Nat.cast_add, Nat.cast_one, prefix_split
      ((c:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))
      (((c:ℝ)+1)*(HigherHeatDyadicLaws.duration 1 n:ℝ))
      (mul_nonneg (Nat.cast_nonneg c) hd) (by nlinarith)]
    change segment ((c:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))
        (((c:ℝ)+1)*(HigherHeatDyadicLaws.duration 1 n:ℝ))
        (pairing m hm T hT (core (cylinderOf n F))) + _ = _
    exact add_comm _ _

theorem derivative_prefix (n c : ℕ) (j : Fin (size n)) :
    polynomialDerivative (Pi.single j 1) (prefixPolynomial n c) =
      if j.val < c then 1 else 0 := by
  classical
  simp [prefixPolynomial, map_sum, polynomialDerivative_X, Pi.single_apply]

theorem second_derivative_prefix (n c : ℕ) (j : Fin (size n)) :
    polynomialDerivative (Pi.single j 1)
      (polynomialDerivative (Pi.single j 1) (prefixPolynomial n c)) = 0 := by
  have h1 : polynomialDerivative (Pi.single j 1) (1:Test n) = 0 := by
    simpa only [MvPolynomial.C_1] using polynomialDerivative_C (Pi.single j 1) (1:ℝ)
  rw [derivative_prefix]
  split_ifs <;> simp only [h1, map_zero]

theorem prefix_square_identity (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (c : ℕ) (hc : c ≤ size n) :
    pairing 2 (by norm_num) T hT (core (cylinderOf n ((prefixPolynomial n c)^2))) =
      firstChannel 2 T (segment 0 ((c:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))
        (pairing 2 (by norm_num) T hT (core (cylinderOf n (prefixPolynomial n c))))) +
      secondChannel 2 T (segment 0 ((c:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))
        (pairing 2 (by norm_num) T hT (core (cylinderOf n (1:Test n))))) := by
  classical
  have hp : (prefixPolynomial n c)^2 =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (size n) => j.val < c),
        prefixPolynomial n c * MvPolynomial.X j := by
    rw [pow_two]
    conv_lhs => rhs; unfold prefixPolynomial
    rw [Finset.mul_sum]
  rw [← coefficient_prefix n 2 (by norm_num) T hT c hc (prefixPolynomial n c),
    ← coefficient_prefix n 2 (by norm_num) T hT c hc (1:Test n)]
  simp only [hp, map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := (Finset.mem_filter.mp hj).2
  have he := affine_agreement_dual n 2 (by norm_num) T hT j (prefixPolynomial n c)
    (second_derivative_prefix n c j)
  rw [derivative_prefix, ite_eq_left hj'] at he
  exact he

end OperatorDerivativeRewrite.Foundation.HigherHeatPrefixSquareIdentity
