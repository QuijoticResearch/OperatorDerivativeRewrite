import Foundation.GaussianSensitivityCore

/-! Continuous sensitivity and stochastic-volatility rigidity on the explicit
adapted polynomial graph completion. No equality with the independent full
predictable Sobolev domain is assumed or asserted. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianContinuousRigidity
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianProductDerivative
open GaussianDerivativeTimeCoordinates GaussianPredictableFull SeparableHilbertEmbedding
open GaussianSensitivityIntegral GaussianTimeDivergence GaussianAdaptedGraphCore
open GaussianTimeSensitivity GaussianSensitivityCore
attribute [local instance] timeHilbert_secondCountable coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

/-- The actual time field embedded in the existing coefficient-Hilbert-space-valued Gaussian L2. -/
def fieldEmbedding : TimeProbabilityL2 →ₗᵢ[ℝ] GaussianVectorL2 :=
  outputEmbedding.comp scalarCurry.toLinearIsometry

theorem fieldEmbedding_tensor (a : TimeHilbert) (f : GaussianL2) :
    fieldEmbedding (GaussianTimeProductL2.productTensor a f) =
      scalarTensor (hilbertEmbedding TimeHilbert a) f := by
  change outputEmbedding (scalarCurry (GaussianTimeProductL2.productTensor a f)) = _
  rw [scalarCurry_productTensor]
  change BochnerLinearIsometry.lift gaussianProduct (hilbertEmbedding TimeHilbert)
    (ProductL2Curry.flip volume gaussianProduct (BochnerClosedOperator.tensor volume a f)) = _
  rw [ProductL2Curry.flip_tensor, BochnerLinearIsometry.lift_tensor]
  rfl

/-- An ambient continuous map used only to pass closed graph relations to limits. -/
def integralExtension : TimeProbabilityL2 →L[ℝ] GaussianL2 :=
  itoIntegral.toContinuousLinearMap.comp fullPredictable.orthogonalProjectionOnto

theorem integralExtension_eq (u : fullPredictable) : integralExtension u = itoIntegral u := by
  change itoIntegral (fullPredictable.orthogonalProjectionOnto u) = _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

def sensitivityMap : (TimeProbabilityL2 × ProductDerivativeL2) →L[ℝ]
    (GaussianL2 × GaussianVectorL2) :=
  (integralExtension.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (fieldEmbedding.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ _ _) +
      correction.comp (ContinuousLinearMap.snd ℝ _ _))

theorem completedGraph_sensitivity {z : TimeProbabilityL2 × ProductDerivativeL2}
    (hz : z ∈ completedGraph) :
    (itoIntegral ⟨z.1, completedGraph_predictable hz⟩,
      fieldEmbedding z.1 + correction z.2) ∈ closedCylindricalDerivative.graph := by
  have h : completedGraph ≤ closedCylindricalDerivative.graph.comap sensitivityMap.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro z ⟨n, s, t, r, p, hrs, hst, rfl⟩
      change (integralExtension (pastStep s t r hrs p),
        fieldEmbedding (GaussianTimeProductL2.productTensor (intervalVector s t)
          (pastCoefficient r p)) + correction (stepGradient s t r p)) ∈
            closedCylindricalDerivative.graph
      rw [integralExtension_eq, ito_pastStep s t hst, fieldEmbedding_tensor,
        correction_stepGradient s t hst r hrs p]
      exact incrementProduct_closedDerivative_graph r p s t hst
    · exact closedCylindricalDerivative_isClosed.preimage sensitivityMap.continuous
  have hh := h hz
  change (integralExtension z.1, fieldEmbedding z.1 + correction z.2) ∈
    closedCylindricalDerivative.graph at hh
  rw [show integralExtension z.1 = itoIntegral ⟨z.1, completedGraph_predictable hz⟩ from
    integralExtension_eq ⟨z.1, completedGraph_predictable hz⟩] at hh
  exact hh

theorem integral_mem_derivative_domain {z : TimeProbabilityL2 × ProductDerivativeL2}
    (hz : z ∈ completedGraph) :
    itoIntegral ⟨z.1, completedGraph_predictable hz⟩ ∈ closedCylindricalDerivative.domain :=
  LinearPMap.mem_domain_iff.mpr ⟨_, completedGraph_sensitivity hz⟩

/-- The full derivative, not a predictable projection, equals the original field
exactly when that field has one deterministic L2 time profile. -/
theorem rigidity_graph {z : TimeProbabilityL2 × ProductDerivativeL2}
    (hz : z ∈ completedGraph) :
    (itoIntegral ⟨z.1, completedGraph_predictable hz⟩, fieldEmbedding z.1) ∈
      closedCylindricalDerivative.graph ↔
        ∃ a : TimeHilbert, z.1 = GaussianTimeProductL2.productTensor a gaussianOne := by
  constructor
  · intro h
    have he := closedCylindricalDerivative.mem_graph_snd_inj (completedGraph_sensitivity hz) h rfl
    have hc : correction z.2 = 0 := by
      exact add_left_cancel (he.trans (add_zero _).symm)
    have hv := (correction_eq_zero_iff z.2 (completedGraph_admissible hz)).mp hc
    apply (derivative_zero_iff_deterministic z.1).mp
    have hg : (z.1, z.2) ∈ derivative.graph := completedGraph_le_derivative hz
    rwa [hv] at hg
  · intro hdet
    have hzero := (derivative_zero_iff_deterministic z.1).mpr hdet
    have hv := derivative.mem_graph_snd_inj (completedGraph_le_derivative hz) hzero rfl
    simpa only [hv, map_zero, add_zero] using completedGraph_sensitivity hz

theorem rigidity_value {z : TimeProbabilityL2 × ProductDerivativeL2}
    (hz : z ∈ completedGraph) :
    closedCylindricalDerivative
      ⟨itoIntegral ⟨z.1, completedGraph_predictable hz⟩, integral_mem_derivative_domain hz⟩ =
        fieldEmbedding z.1 ↔
          ∃ a : TimeHilbert, z.1 = GaussianTimeProductL2.productTensor a gaussianOne := by
  rw [← rigidity_graph hz]
  constructor
  · intro h
    have hg := closedCylindricalDerivative.mem_graph
      ⟨itoIntegral ⟨z.1, completedGraph_predictable hz⟩, integral_mem_derivative_domain hz⟩
    simpa only [h] using hg
  · intro h
    exact closedCylindricalDerivative.mem_graph_snd_inj
      (closedCylindricalDerivative.mem_graph _) h rfl

end OperatorDerivativeRewrite.Foundation.GaussianContinuousRigidity
