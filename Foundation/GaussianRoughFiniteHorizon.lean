import Foundation.GaussianPredictableDomainGap
import Foundation.GaussianConditionalClarkOcone

/-! Finite-horizon representation does not require the full Gaussian adjoint domain. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianRoughFiniteHorizon
open InfiniteGaussian GaussianTimeProductL2 GaussianPredictableFull
open GaussianPredictableAdjoint GaussianPredictableCutoff GaussianConditionalIto
open GaussianConditionalClarkOcone GaussianPredictableDomainGap PredictableRealL2
set_option backward.isDefEq.respectTransparency false

/-- Restriction uses the independently defined predictable L2 space on (0,T]. -/
def restrictPredictable (T : ℝ≥0) (U : fullPredictable) :
    GaussianPredictableHorizon.PredictableDomain T :=
  ⟨LpToLpRestrictCLM _ ℝ ℝ timeProbability 2 (horizon T) U,
    U.property.1.restrict.congr
      (LpToLpRestrictCLM_coeFn ℝ (horizon T) (U : TimeProbabilityL2)).symm⟩

theorem restricted_integral (T : ℝ≥0) (U : fullPredictable) :
    GaussianPredictableHorizon.itoIntegral T (restrictPredictable T U) =
      GaussianPredictableFull.itoIntegral (predictableCut T U) := by
  change GaussianPredictableL2Completion.productIntegral _ =
    GaussianPredictableL2Completion.productIntegral _
  congr 1

theorem finite_horizon_representation (T : ℝ≥0) (F : GaussianL2)
    (hF : F ∈ pastL2 T) :
    ∃! U : GaussianPredictableHorizon.PredictableDomain T,
      GaussianPredictableHorizon.itoIntegral T U =
        F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  refine ⟨restrictPredictable T (predictableAdjoint F), ?_, ?_⟩
  · dsimp only
    rw [restricted_integral, past_representer_supported T F hF]
    exact GaussianBrownianPRP.brownian_representation F (past_mem_brownian T hF)
  · intro U hU
    apply (GaussianPredictableHorizon.itoIntegral T).injective
    exact hU.trans (by
      rw [restricted_integral, past_representer_supported T F hF]
      exact (GaussianBrownianPRP.brownian_representation F
        (past_mem_brownian T hF)).symm)

theorem terminalSigma_le_past : terminalSigma ≤ GaussianTimeProcess.naturalFiltration 1 := by
  exact (GaussianTimeProcess.process_stronglyAdapted 1).measurable.comap_le

theorem rough_mem_past : roughTerminal terminalDirection terminalDirection_unit ∈ pastL2 1 :=
  rough_terminal_mem.mono terminalSigma_le_past

theorem rough_representer_supported :
    predictableCut 1 (predictableAdjoint (roughTerminal terminalDirection terminalDirection_unit)) =
      predictableAdjoint (roughTerminal terminalDirection terminalDirection_unit) :=
  past_representer_supported 1 _ rough_mem_past

theorem rough_finite_representation_without_full_adjoint :
    ∃ F : GaussianL2, F ∈ pastL2 1 ∧ F ∉ hilbertDivergence.adjoint.domain ∧
      ∃! U : GaussianPredictableHorizon.PredictableDomain 1,
        GaussianPredictableHorizon.itoIntegral 1 U =
          F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  exact ⟨roughTerminal terminalDirection terminalDirection_unit, rough_mem_past,
    rough_not_in_full_adjoint_domain terminalDirection terminalDirection_unit,
    finite_horizon_representation 1 _ rough_mem_past⟩

end OperatorDerivativeRewrite.Foundation.GaussianRoughFiniteHorizon
