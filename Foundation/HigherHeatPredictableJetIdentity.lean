import Foundation.HigherHeatPredictableJetBounds
import Foundation.HigherHeatInnovationMoments

/-! Identification of the uniformly bounded jets with actual native conditional
increments and signed one-step Taylor innovations. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPredictableJetIdentity
open HigherHeatPolynomialCylinders HigherHeatPredictableJetBounds HigherHeatDyadicConditioning
open PureOrderPolynomialConditioning SingleCoordinateConditioning MultivariateDirectionalKernel
open HigherHeatMultivariateMoments PureOrderTaylorInnovations

def slice (n m : ℕ) (T : ℝ≥0) (j : Fin (size n)) (P : Test n)
    (x : Fin (size n) → ℝ) : Polynomial ℝ :=
  line (Pi.single j 1) (basePoint n j x) (nextConditioned n m T j P)

theorem base_erase_agree (n : ℕ) (j : Fin (size n)) (x : Fin (size n) → ℝ)
    (i : Fin (size n)) (hi : i ∈ initialPast n (j.val+1)) :
    basePoint n j x i = eraseValue j x i := by
  have hi' : i.val ≤ j.val := by
    have h := (Finset.mem_filter.mp hi).2
    omega
  by_cases hij : i=j
  · subst i
    simp [basePoint, eraseValue]
  · have hlt : i < j := by
      change i.val < j.val
      have hn : i.val ≠ j.val := by simpa [Fin.ext_iff] using hij
      omega
    simp [basePoint, hlt, eraseValue, hij]

theorem slice_eq_erased_line (n m : ℕ) (T : ℝ≥0) (j : Fin (size n)) (P : Test n)
    (x : Fin (size n) → ℝ) :
    slice n m T j P x = line (Pi.single j 1) (eraseValue j x) (nextConditioned n m T j P) := by
  apply Polynomial.funext
  intro z
  rw [slice, eval_line, eval_line]
  apply Complex.ofReal_injective
  apply conditioning_dependsOn (2*m) (parameters m (fun _ => HigherHeatDyadicLaws.duration T n))
    (initialPast n (j.val+1)) P
  intro i hi
  rw [base_erase_agree n j x i hi]

theorem slice_at_current (n m : ℕ) (T : ℝ≥0) (j : Fin (size n)) (P : Test n)
    (x : Fin (size n) → ℝ) :
    (slice n m T j P x).eval (x j) = MvPolynomial.eval x (nextConditioned n m T j P) := by
  rw [slice, eval_line]
  apply Complex.ofReal_injective
  apply conditioning_dependsOn (2*m) (parameters m (fun _ => HigherHeatDyadicLaws.duration T n))
    (initialPast n (j.val+1)) P
  intro i hi
  have hi' : i.val ≤ j.val := by have h := (Finset.mem_filter.mp hi).2; omega
  by_cases hij : i=j
  · subst i
    simp [basePoint]
  · have hlt : i < j := by
      change i.val < j.val
      have hn : i.val ≠ j.val := by simpa [Fin.ext_iff] using hij
      omega
    simp [basePoint, hlt, hij]

theorem slice_expectation (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (j : Fin (size n))
    (P : Test n) (x : Fin (size n) → ℝ) :
    PseudoPolynomialStein.expectation (2*m)
      ((-1:ℝ)^(m+1)*(HigherHeatDyadicLaws.duration T n:ℝ)) (slice n m T j P x) =
      MvPolynomial.eval x (localProjection m T n (initialPast n j.val) P) := by
  classical
  rw [slice_eq_erased_line, expectation_polynomialEvolution (2*m) (by omega)]
  change MvPolynomial.eval (eraseValue j x)
    (MultivariateDirectionalKernel.transport (2*m) (by omega)
      (parameters m (fun _ => HigherHeatDyadicLaws.duration T n) j)
      (Pi.single j 1) (nextConditioned n m T j P)) = _
  rw [← eval_zeroCoordinate, heat_then_zero, nextConditioned, localProjection, conditioning_tower]
  apply congrArg (fun S : Finset (Fin (size n)) => MvPolynomial.eval x
    (conditioning (2*m) (parameters m (fun _ => HigherHeatDyadicLaws.duration T n)) S P))
  ext i
  simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true,
    initialPast, Finset.mem_filter, true_and, Fin.ext_iff]
  omega

theorem actual_step (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (j : Fin (size n))
    (P : Test n) (x : Fin (size n) → ℝ) :
    MvPolynomial.eval x (nextConditioned n m T j P)-
      MvPolynomial.eval x (localProjection m T n (initialPast n j.val) P) =
      ∑ q ∈ Finset.range ((slice n m T j P x).natDegree+1),
        MvPolynomial.eval x (predictableJet n m T j q P)*
          ((x j)^q-HigherHeatInnovationMoments.cellMoment n m T q) := by
  have h := congrArg (fun R : Polynomial ℝ => R.eval (x j))
    (centered_expansion (2*m)
      ((-1:ℝ)^(m+1)*(HigherHeatDyadicLaws.duration T n:ℝ)) (slice n m T j P x))
  simp only [centering_apply, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_smul, innovation, Polynomial.eval_pow,
    Polynomial.eval_X, smul_eq_mul, slice_at_current, slice_expectation n m hm T j P x] at h
  simpa only [predictable_jet_coefficient, slice, HigherHeatInnovationMoments.cellMoment] using h

theorem actual_kernel_step (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (P : Test n) (x : Fin (size n) → ℝ) :
    MvPolynomial.eval x (nextConditioned n m T j P)-
      HigherHeatPolynomialRealization.kernelExpectation m hm (HigherHeatDyadicLaws.duration T n)
        (HigherHeatDyadicLaws.duration_pos T hT n) (slice n m T j P x) =
      ∑ q ∈ Finset.range ((slice n m T j P x).natDegree+1),
        MvPolynomial.eval x (predictableJet n m T j q P)*
          ((x j)^q-HigherHeatInnovationMoments.cellMoment n m T q) := by
  rw [HigherHeatPolynomialRealization.kernelExpectation_eq_moments, slice_expectation n m hm T j P x]
  exact actual_step n m hm T j P x

end OperatorDerivativeRewrite.Foundation.HigherHeatPredictableJetIdentity
