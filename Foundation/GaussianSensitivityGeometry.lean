import Foundation.GaussianQuantitativeRigidity

/-! Orthogonality and exact energy for the full predictable Sobolev sensitivity
formula. The correction is orthogonal to every embedded predictable field. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianSensitivityGeometry
open InfiniteGaussian GaussianTimeProductL2 GaussianProductDerivative GaussianPredictableFull
open GaussianPredictableChaosCore GaussianContinuousRigidity GaussianPredictableAdjoint
open GaussianSensitivityIntegral
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

theorem predictableProjection_field (u : fullPredictable) :
    predictableProjection (fieldEmbedding u) = u :=
  congrArg (fun L : fullPredictable →L[ℝ] fullPredictable => L u) predictableField.adjoint_comp_self

theorem correction_predictableProjection_zero (u : fullPredictable) (v : ProductDerivativeL2)
    (hd : ((u : TimeProbabilityL2), v) ∈ derivative.graph) :
    predictableProjection (correction v) = 0 := by
  have h := predictableAdjoint_eq_projected_derivative (independentIntegralDomain u v hd)
  change predictableAdjoint (itoIntegral u) =
    predictableProjection (closedCylindricalDerivative (independentIntegralDomain u v hd)) at h
  rw [predictableAdjoint_integral, independent_sensitivity_value, map_add,
    predictableProjection_field] at h
  exact add_left_cancel (h.symm.trans (add_zero u).symm)

theorem correction_orthogonal_predictable (u : fullPredictable) (v : ProductDerivativeL2)
    (hd : ((u : TimeProbabilityL2), v) ∈ derivative.graph) (w : fullPredictable) :
    inner ℝ (correction v) (fieldEmbedding w) = 0 := by
  have h := congrArg (fun z : fullPredictable => inner ℝ z w)
    (correction_predictableProjection_zero u v hd)
  change inner ℝ (predictableField.toContinuousLinearMap.adjoint (correction v)) w = _ at h
  rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left] at h
  exact h

theorem sensitivity_energy (u : fullPredictable) (v : ProductDerivativeL2)
    (hd : ((u : TimeProbabilityL2), v) ∈ derivative.graph) :
    ‖closedCylindricalDerivative (independentIntegralDomain u v hd)‖ ^ 2 =
      ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have hc := GaussianSensitivityCore.completedGraph_correction_norm
    (independent_graph_mem_completed u.property hd)
  change ‖correction v‖ = ‖v‖ at hc
  rw [independent_sensitivity_value, norm_add_sq_real, fieldEmbedding.norm_map, hc,
    real_inner_comm (correction v) (fieldEmbedding u), correction_orthogonal_predictable u v hd u]
  simp only [Submodule.norm_coe]
  ring

theorem sensitivity_graph_energy (u : fullPredictable) (v : ProductDerivativeL2)
    (hd : ((u : TimeProbabilityL2), v) ∈ derivative.graph) :
    ‖itoIntegral u‖ ^ 2 +
      ‖closedCylindricalDerivative (independentIntegralDomain u v hd)‖ ^ 2 =
        2 * ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [itoIntegral.norm_map, sensitivity_energy]
  ring

end OperatorDerivativeRewrite.Foundation.GaussianSensitivityGeometry
