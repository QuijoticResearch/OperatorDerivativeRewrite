import Foundation.ProductL2Flip
import Foundation.GaussianAdaptedGraphCore
import Foundation.GaussianParameterizedIntegral

/-! A genuine continuous sensitivity integral on square-integrable predictable
derivative-time families. Its input embedding keeps the complete time field. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianSensitivityIntegral
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianProductDerivative
open GaussianDerivativeTimeCoordinates GaussianPredictableFull SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

/-- The outer parameter is derivative time; each value is an actual predictable integrand. -/
abbrev Inputs := Lp fullPredictable 2 (volume : Measure ℝ)

def inclusion : Inputs →ₗᵢ[ℝ] Lp TimeProbabilityL2 2 (volume : Measure ℝ) :=
  BochnerLinearIsometry.lift volume fullPredictable.subtypeₗᵢ

/-- Actual joint coefficient field of the parameterized predictable integrands. -/
def kernelEmbedding : Inputs →ₗᵢ[ℝ] ProductDerivativeL2 :=
  embedTimeField.comp ((ProductL2Curry.flip volume timeProbability).comp inclusion)

def outputEmbedding : Lp GaussianL2 2 (volume : Measure ℝ) →ₗᵢ[ℝ] GaussianVectorL2 :=
  (BochnerLinearIsometry.lift gaussianProduct (hilbertEmbedding TimeHilbert)).comp
    (ProductL2Curry.flip volume gaussianProduct)

/-- Actual parameterized Ito integration, followed by the same Brownian time embedding. -/
def integral : Inputs →ₗᵢ[ℝ] GaussianVectorL2 :=
  outputEmbedding.comp (GaussianParameterizedIntegral.parameterIntegral volume)

theorem integral_norm (v : Inputs) : ‖integral v‖ = ‖kernelEmbedding v‖ := by
  rw [integral.norm_map, kernelEmbedding.norm_map]

theorem integral_eq_zero_iff (v : Inputs) : integral v = 0 ↔ kernelEmbedding v = 0 := by
  rw [integral.injective.eq_iff' (map_zero _), kernelEmbedding.injective.eq_iff' (map_zero _)]

theorem kernelEmbedding_tensor (a : TimeHilbert) (u : fullPredictable) :
    kernelEmbedding (BochnerClosedOperator.tensor volume a u) =
      BochnerClosedOperator.tensor timeProbability (u : TimeProbabilityL2)
        (hilbertEmbedding TimeHilbert a) := by
  change embedTimeField (ProductL2Curry.flip volume timeProbability
    (BochnerLinearIsometry.lift volume fullPredictable.subtypeₗᵢ
      (BochnerClosedOperator.tensor volume a u))) = _
  rw [BochnerLinearIsometry.lift_tensor, ProductL2Curry.flip_tensor]
  exact BochnerLinearIsometry.lift_tensor _ _ _ _

theorem integral_tensor (a : TimeHilbert) (u : fullPredictable) :
    integral (BochnerClosedOperator.tensor volume a u) =
      scalarTensor (hilbertEmbedding TimeHilbert a) (itoIntegral u) := by
  change BochnerLinearIsometry.lift gaussianProduct (hilbertEmbedding TimeHilbert)
    (ProductL2Curry.flip volume gaussianProduct
      (BochnerLinearIsometry.lift volume itoIntegral (BochnerClosedOperator.tensor volume a u))) = _
  rw [BochnerLinearIsometry.lift_tensor, ProductL2Curry.flip_tensor,
    BochnerLinearIsometry.lift_tensor]
  rfl

/-- The admissible input fields form a closed subspace, since their embedding is isometric. -/
theorem kernelEmbedding_closed_range :
    IsClosed (kernelEmbedding.toLinearMap.range : Set ProductDerivativeL2) :=
  kernelEmbedding.isometry.isClosedEmbedding.isClosed_range

/-- Continuous extension to all fields by orthogonal projection onto the admissible range.
Only on that proved range will it be used as the lossless sensitivity correction. -/
def correction : ProductDerivativeL2 →L[ℝ] GaussianVectorL2 :=
  integral.toContinuousLinearMap.comp kernelEmbedding.toContinuousLinearMap.adjoint

theorem correction_embedding (v : Inputs) : correction (kernelEmbedding v) = integral v := by
  have h := congrArg (fun L : Inputs →L[ℝ] Inputs => L v) kernelEmbedding.adjoint_comp_self
  change kernelEmbedding.toContinuousLinearMap.adjoint (kernelEmbedding v) = v at h
  change integral (kernelEmbedding.toContinuousLinearMap.adjoint (kernelEmbedding v)) = _
  rw [h]

theorem correction_norm (v : ProductDerivativeL2)
    (hv : v ∈ kernelEmbedding.toLinearMap.range) : ‖correction v‖ = ‖v‖ := by
  obtain ⟨w, rfl⟩ := hv
  change ‖correction (kernelEmbedding w)‖ = ‖kernelEmbedding w‖
  rw [correction_embedding, integral_norm]

theorem correction_eq_zero_iff (v : ProductDerivativeL2)
    (hv : v ∈ kernelEmbedding.toLinearMap.range) : correction v = 0 ↔ v = 0 := by
  rw [← norm_eq_zero, correction_norm v hv, norm_eq_zero]

end OperatorDerivativeRewrite.Foundation.GaussianSensitivityIntegral
