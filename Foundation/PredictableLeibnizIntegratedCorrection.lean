import Foundation.PredictableLeibnizCounterexample
import Foundation.IntegratedBrownianStatePrediction
import Foundation.GaussianDeterministicVolterra

/-! The cubic conditional-Leibniz defect is exactly the predictable adjoint of
twice the existing integrated-Brownian ramp observable. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PredictableLeibnizIntegratedCorrection
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianPredictableFull
open GaussianPredictableAdjoint GaussianProductDerivative GaussianDeterministicIntegral
open GaussianDeterministicVolterra IntegratedBrownianStatePrediction
open PredictableLeibnizCounterexample GaussianCubicDiagnostic
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

def integratedTerminal (T : ℝ≥0) : GaussianL2 :=
  GaussianHilbertProcess.isonormalEmbedding TimeHilbert (integratedVector T)

theorem integratedProfile_predictable (T : ℝ≥0) :
    productTensor (integratedVector T) gaussianOne ∈ fullPredictable := by
  apply positive_profile_predictable
  filter_upwards [integratedVector_coeFn T] with x hx hnon
  rw [hx]
  have hnot : x ∉ Ioc 0 (T : ℝ) := fun h => (not_lt.mpr hnon) h.1
  simp [hnot]

theorem integratedTerminal_adjoint (T : ℝ≥0) :
    predictableAdjoint (integratedTerminal T) =
      ⟨productTensor (integratedVector T) gaussianOne, integratedProfile_predictable T⟩ := by
  unfold integratedTerminal
  exact predictableAdjoint_deterministic_firstChaos _ (integratedProfile_predictable T)

theorem integratedTerminal_adjoint_slices (T : ℝ≥0) :
    scalarCurry (predictableAdjoint (integratedTerminal T) : TimeProbabilityL2) =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator (fun x => ((T : ℝ)-x) • gaussianOne) := by
  rw [integratedTerminal_adjoint]
  change scalarCurry (productTensor (integratedVector T) gaussianOne) =ᵐ[volume] _
  rw [scalarCurry_productTensor]
  filter_upwards [BochnerClosedOperator.tensor_coeFn volume (integratedVector T) gaussianOne,
    integratedVector_coeFn T] with x ht hx
  rw [ht, hx]
  by_cases h : x ∈ Ioc 0 (T : ℝ) <;> simp [h]

theorem cubic_defect_eq_integrated_adjoint (T : ℝ≥0) :
    cubicAdjoint T - conditionalLeibnizCandidate T =
      (2 : ℝ) • scalarCurry (predictableAdjoint (integratedTerminal T) : TimeProbabilityL2) := by
  have he : cubicAdjoint T - conditionalLeibnizCandidate T =
      (2/3 : ℝ) • (cubicAdjoint T - cubicSpatial T) := by
    rw [conditionalLeibnizCandidate]
    module
  rw [he]
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (2/3 : ℝ) (cubicAdjoint T-cubicSpatial T),
    cubic_projection_difference_slices T,
    Lp.coeFn_smul (2 : ℝ) (scalarCurry (predictableAdjoint (integratedTerminal T) : TimeProbabilityL2)),
    integratedTerminal_adjoint_slices T] with x hs hc ht hi
  rw [hs, ht, Pi.smul_apply, Pi.smul_apply]
  change (2/3 : ℝ) • (scalarCurry (predictableAdjoint
    (GaussianScalarPolynomialIto.polynomialValue T (Polynomial.X^3)) : TimeProbabilityL2) -
      GaussianPolynomialIto.spatialField T (GaussianPolynomialDifferentiation.spatialPolynomial (Polynomial.X^3))) x = _
  rw [hc, hi]
  by_cases h : x ∈ Ioc 0 (T : ℝ)
  · simp only [indicator_of_mem h]
    module
  · simp [h]

end OperatorDerivativeRewrite.Foundation.PredictableLeibnizIntegratedCorrection
