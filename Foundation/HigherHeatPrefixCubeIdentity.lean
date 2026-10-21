import Foundation.HigherHeatPrefixSquareIdentity
import Foundation.HigherHeatCubicStepIdentity

/-! Exact signed three-channel identification of native cubic prefixes. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPrefixCubeIdentity
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement HigherHeatSecondChannelSteps
open HigherHeatThirdChannelSteps HigherHeatPrefixFields HigherHeatQuadraticItoData
open HigherHeatPrefixSquareIdentity MultivariateFactorialDomain MultivariateFactorialSubstitution
open HigherHeatCubicStepIdentity

theorem derivative_prefix_square (n c : ℕ) (j : Fin (size n)) (hj : j.val < c) :
    polynomialDerivative (Pi.single j 1) ((prefixPolynomial n c)^2) =
      (2:ℕ) • prefixPolynomial n c := by
  rw [pow_two, Derivation.leibniz]
  simp only [derivative_prefix, ite_eq_left hj, smul_eq_mul, mul_one, two_nsmul]

theorem second_derivative_prefix_square (n c : ℕ) (j : Fin (size n)) (hj : j.val < c) :
    polynomialDerivative (Pi.single j 1)
      (polynomialDerivative (Pi.single j 1) ((prefixPolynomial n c)^2)) = (2:ℕ) • (1:Test n) := by
  rw [derivative_prefix_square n c j hj, map_nsmul, derivative_prefix, ite_eq_left hj]

theorem third_derivative_prefix_square (n c : ℕ) (j : Fin (size n)) :
    (polynomialDerivative (Pi.single j 1) : Test n → Test n)^[3] ((prefixPolynomial n c)^2) = 0 := by
  by_cases hj : j.val < c
  · change polynomialDerivative (Pi.single j 1)
      (polynomialDerivative (Pi.single j 1)
        (polynomialDerivative (Pi.single j 1) ((prefixPolynomial n c)^2))) = 0
    rw [second_derivative_prefix_square n c j hj, map_nsmul]
    have h1 : polynomialDerivative (Pi.single j 1) (1:Test n) = 0 := by
      simpa only [MvPolynomial.C_1] using polynomialDerivative_C (Pi.single j 1) (1:ℝ)
    rw [h1, nsmul_zero]
  · have hd : polynomialDerivative (Pi.single j 1) ((prefixPolynomial n c)^2) = 0 := by
      rw [pow_two, Derivation.leibniz]
      simp only [derivative_prefix, ite_eq_right hj, smul_eq_mul, mul_zero, add_zero]
    change polynomialDerivative (Pi.single j 1) (polynomialDerivative (Pi.single j 1)
      (polynomialDerivative (Pi.single j 1) ((prefixPolynomial n c)^2))) = 0
    rw [hd, map_zero, map_zero]

theorem prefix_cube_identity (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (c : ℕ) (hc : c ≤ size n) :
    pairing 2 (by norm_num) T hT (core (cylinderOf n ((prefixPolynomial n c)^3))) =
      firstChannel 2 T (segment 0 ((c:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))
        (pairing 2 (by norm_num) T hT (core (cylinderOf n ((prefixPolynomial n c)^2))))) +
      (2:ℕ) • secondChannel 2 T (segment 0 ((c:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))
        (pairing 2 (by norm_num) T hT (core (cylinderOf n (prefixPolynomial n c))))) +
      thirdChannel T (segment 0 ((c:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))
        (pairing 2 (by norm_num) T hT (core (cylinderOf n (1:Test n))))) := by
  classical
  have hp : (prefixPolynomial n c)^3 =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (size n) => j.val < c),
        (prefixPolynomial n c)^2 * MvPolynomial.X j := by
    rw [pow_succ]
    conv_lhs => rhs; unfold prefixPolynomial
    rw [Finset.mul_sum]
  rw [← coefficient_prefix n 2 (by norm_num) T hT c hc ((prefixPolynomial n c)^2),
    ← coefficient_prefix n 2 (by norm_num) T hT c hc (prefixPolynomial n c),
    ← coefficient_prefix n 2 (by norm_num) T hT c hc (1:Test n)]
  simp only [hp, map_sum, Finset.smul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := (Finset.mem_filter.mp hj).2
  have he := quadratic_agreement_dual n T hT j ((prefixPolynomial n c)^2)
    (third_derivative_prefix_square n c j)
  rw [second_derivative_prefix_square n c j hj', derivative_prefix_square n c j hj'] at he
  simpa only [two_nsmul, coefficientField_add, map_add, smul_add, ← add_smul,
    show (1/2:ℝ)+(1/2:ℝ)=1 by norm_num, one_smul] using he

end OperatorDerivativeRewrite.Foundation.HigherHeatPrefixCubeIdentity
