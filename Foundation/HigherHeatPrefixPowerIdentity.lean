import Foundation.HigherHeatPrefixSquareIdentity
import Foundation.HigherHeatAllPowerSteps

/-! Exact signed prefix-power recursion for every polynomial degree and even order. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPrefixPowerIdentity
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement HigherHeatPrefixFields
open HigherHeatQuadraticItoData HigherHeatPrefixSquareIdentity HigherHeatAllProductChannels
open HigherHeatAllPowerSteps HigherHeatMonomialJets MultivariateFactorialDomain

theorem prefix_power_jets (n c : ℕ) (j : Fin (size n)) (hj : j.val < c) (r k : ℕ) :
    (polynomialDerivative (Pi.single j 1) : Test n → Test n)^[k] ((prefixPolynomial n c)^r) =
      r.descFactorial k • (prefixPolynomial n c)^(r-k) := by
  have h1 : polynomialDerivative (Pi.single j 1) (1:Test n) = 0 :=
    Derivation.map_one_eq_zero _
  have hP : polynomialDerivative (Pi.single j 1) (prefixPolynomial n c) = 1 := by
    rw [derivative_prefix, ite_eq_left hj]
  simpa only [one_mul] using derivative_iterate_mul_power (Pi.single j 1)
    (1:Test n) (prefixPolynomial n c) h1 hP r k

theorem prefix_power_identity (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (c : ℕ) (hc : c ≤ size n) (r : ℕ) :
    pairing m hm T hT (core (cylinderOf n ((prefixPolynomial n c)^(r+1)))) =
      ∑ k ∈ Finset.range (2*m), r.descFactorial k • productChannel m T k
        (segment 0 ((c:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))
          (pairing m hm T hT (core (cylinderOf n ((prefixPolynomial n c)^(r-k)))))) := by
  classical
  have hp : (prefixPolynomial n c)^(r+1) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (size n) => j.val < c),
        (prefixPolynomial n c)^r * MvPolynomial.X j := by
    rw [pow_succ]
    conv_lhs => rhs; unfold prefixPolynomial
    rw [Finset.mul_sum]
  rw [hp]
  simp only [map_sum]
  calc
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin (size n) => j.val < c),
        ∑ k ∈ Finset.range (2*m), r.descFactorial k • productChannel m T k
          (coefficientField n m hm T hT j ((prefixPolynomial n c)^(r-k))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [agreement_dual, correction]
      simp only [prefix_power_jets n c j (Finset.mem_filter.mp hj).2,
        coefficientField_nsmul, map_nsmul]
    _ = ∑ k ∈ Finset.range (2*m), r.descFactorial k • productChannel m T k
        (∑ j ∈ Finset.univ.filter (fun j : Fin (size n) => j.val < c),
          coefficientField n m hm T hT j ((prefixPolynomial n c)^(r-k))) := by
      rw [Finset.sum_comm]
      simp only [map_sum, Finset.smul_sum]
    _ = _ := by simp_rw [coefficient_prefix n m hm T hT c hc]

end OperatorDerivativeRewrite.Foundation.HigherHeatPrefixPowerIdentity
