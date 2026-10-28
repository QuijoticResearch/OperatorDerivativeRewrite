import Foundation.SU2OneWordLargeCoupling

noncomputable section
namespace OperatorDerivativeRewrite.Foundation.SU2OpenLinkGaugeObstruction
open QuaternionSU2Representation SU2TraceHessianModel

def EndpointInvariant (f : SU2 → ℝ) : Prop :=
  ∀ g h A : SU2, f (g * A * h⁻¹) = f A

theorem endpointInvariant_const {f : SU2 → ℝ} (hf : EndpointInvariant f) (A : SU2) :
    f A = f (1 : SU2) := by
  simpa [EndpointInvariant] using hf A 1 1

theorem halfTrace_one : halfTrace (1 : SU2) = 1 := by
  norm_num [halfTrace, SU2TraceHessianModel.traceReal, Matrix.trace_fin_two,
    Matrix.one_apply]

theorem halfTrace_minusOne : halfTrace SU2StapleExtremes.minusOne = -1 := by
  norm_num [halfTrace, SU2StapleExtremes.minusOne,
    QuaternionSU2Representation.hom, QuaternionSU2Representation.repr,
    SU2TraceHessianModel.traceReal, Matrix.trace_fin_two]

theorem halfTrace_not_endpointInvariant : ¬ EndpointInvariant halfTrace := by
  intro hf
  have h := endpointInvariant_const hf SU2StapleExtremes.minusOne
  rw [halfTrace_minusOne, halfTrace_one] at h
  norm_num at h

end OperatorDerivativeRewrite.Foundation.SU2OpenLinkGaugeObstruction

namespace OperatorDerivativeRewrite.Foundation.SU2OpenLinkGaugeObstruction
open QuaternionSU2Representation SU2TraceHessianModel

def closedPairTrace (A B : SU2) : ℝ := halfTrace (A * B)

theorem closedPairTrace_gauge (g h A B : SU2) :
    closedPairTrace (g * A * h⁻¹) (h * B * g⁻¹) = closedPairTrace A B := by
  unfold closedPairTrace
  have he : (g * A * h⁻¹) * (h * B * g⁻¹) = g * (A * B) * g⁻¹ := by group
  rw [he, halfTrace_conjugate]

theorem closedPairTrace_nonconstant :
    closedPairTrace SU2StapleExtremes.minusOne 1 ≠ closedPairTrace 1 1 := by
  norm_num [closedPairTrace, halfTrace_minusOne, halfTrace_one]

end OperatorDerivativeRewrite.Foundation.SU2OpenLinkGaugeObstruction

namespace OperatorDerivativeRewrite.Foundation.SU2OpenLinkGaugeObstruction
open MeasureTheory ProbabilityTheory QuaternionSU2Representation

theorem endpointInvariant_integral (μ : Measure SU2) [IsProbabilityMeasure μ]
    {f : SU2 → ℝ} (hf : EndpointInvariant f) :
    (∫ A, f A ∂μ) = f (1 : SU2) := by
  have he : f = fun _ => f (1 : SU2) := funext (endpointInvariant_const hf)
  rw [he]
  simp

theorem endpointInvariant_transfer_mean (ν : Measure SU2) [IsProbabilityMeasure ν]
    (β : ℝ) (A B : SU2) {f : SU2 → ℝ} (hf : EndpointInvariant f) :
    (∫ C, f C ∂SU2OneWordTransfer.transition ν β A) =
      (∫ C, f C ∂SU2OneWordTransfer.transition ν β B) := by
  letI : IsMarkovKernel (SU2OneWordTransfer.transition ν β) :=
    SU2OneWordTransfer.transition_markov ν β
  rw [endpointInvariant_integral (SU2OneWordTransfer.transition ν β A) hf,
      endpointInvariant_integral (SU2OneWordTransfer.transition ν β B) hf]

end OperatorDerivativeRewrite.Foundation.SU2OpenLinkGaugeObstruction
