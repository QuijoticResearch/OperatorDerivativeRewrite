import Foundation.RetainedCoordinateDifferentiation
import Foundation.HigherHeatJetCorrectionFields

/-! Exact causal meaning of the one-cell heat-shifted Taylor jet, followed by
its genuine L1 approximation on refinements of every fixed multitime input. -/
noncomputable section
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCausalJetIdentification
open Filter HigherHeatPolynomialCylinders HigherHeatPredictableJetBounds
open HigherHeatDyadicConditioning PureOrderPolynomialConditioning
open MultivariateFactorialDomain MultivariateDirectionalKernel
open HigherHeatPredictableJetIdentity HigherHeatJetHeatCorrection
open HigherHeatDyadicStepAgreement HigherHeatWeakTimeAdjoint HigherHeatRefinedPredictableJets

theorem derivative_next (n m : ℕ) (T : ℝ≥0) (j : Fin (size n))
    (q : ℕ) (P : Test n) :
    (polynomialDerivative (Pi.single j 1) : Test n → Test n)^[q]
        (nextConditioned n m T j P) =
      nextConditioned n m T j
        ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[q] P) := by
  exact RetainedCoordinateDifferentiation.iterate_conditioning (2*m)
    (parameters m (fun _ => HigherHeatDyadicLaws.duration T n)) _ j
    (by simp [initialPast]) q P

theorem heat_then_clamp_next (n m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (j : Fin (size n)) (P : Test n) :
    clampBefore n j (transport (2*m) (by omega)
      ((-1:ℝ)^(m+1)*(HigherHeatDyadicLaws.duration T n:ℝ))
      (Pi.single j 1) (nextConditioned n m T j P)) =
      localProjection m T n (initialPast n j.val) P := by
  apply MvPolynomial.funext
  intro x
  rw [eval_clampBefore]
  change MvPolynomial.eval (basePoint n j x)
    (MultivariateFactorialHeat.polynomialEvolution (2*m)
      ((-1:ℝ)^(m+1)*(HigherHeatDyadicLaws.duration T n:ℝ))
      (Pi.single j 1) (nextConditioned n m T j P)) = _
  rw [← expectation_polynomialEvolution (2*m) (by omega)]
  exact slice_expectation n m hm T j P x

def causalJet (n m : ℕ) (T : ℝ≥0) (j : Fin (size n)) (q : ℕ) (P : Test n) : Test n :=
  (q.factorial:ℝ)⁻¹ • localProjection m T n (initialPast n j.val)
    ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[q] P)

theorem physical_shifted_jet_eq (n m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (j : Fin (size n)) (q : ℕ) (P : Test n) :
    shiftedJet n m hm T j q
      ((-1:ℝ)^(m+1)*(HigherHeatDyadicLaws.duration T n:ℝ)) P =
      causalJet n m T j q P := by
  rw [shiftedJet, derivative_next, heat_then_clamp_next n m hm T]
  rfl

theorem causal_field_approximation (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    Tendsto (fun n =>
      adaptedField n m hm T hT (fun j => causalJet n m T j q (refinedInput b P n)) -
      adaptedField n m hm T hT (fun j => predictableJet n m T j q (refinedInput b P n)))
      atTop (𝓝 (0:Field timeMeasure)) := by
  simpa only [physical_shifted_jet_eq] using
    HigherHeatJetCorrectionFields.physical_cell_error_vanish b P m hm T hT q

end OperatorDerivativeRewrite.Foundation.HigherHeatCausalJetIdentification
