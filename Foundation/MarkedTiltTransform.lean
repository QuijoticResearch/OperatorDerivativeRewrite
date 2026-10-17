import Foundation.ComplexDensityUnbounded
import Foundation.MarkedExponentialTilt
import Foundation.MarkedTwoTimeHolomorphicTransform

/-! Genuine complex tilted holomorphic laws and their shifted generator symbols. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedTiltTransform
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedHolomorphicExponential MarkedExponentialMartingale

theorem weighted_phase_integrable (a ξ η : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    Integrable (fun ω => phase a η s ω * normalized a ξ t ω) probability := by
  have he : (fun ω => phase a η s ω * normalized a ξ t ω) =
      (fun ω => Complex.exp (-(t : ℂ)*symbol a ξ) *
        (phase a η s ω * phase a ξ t ω)) := by
    funext ω
    unfold normalized
    ring
  rw [he]
  exact (MarkedTwoTimeHolomorphicTransform.product_integrable a η ξ s t hst).const_mul _

theorem weighted_phase_mean (a ξ η : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, phase a η s ω * normalized a ξ t ω ∂probability) =
      Complex.exp ((s : ℂ)*(symbol a (η+ξ)-symbol a ξ)) := by
  have he : (fun ω => phase a η s ω * normalized a ξ t ω) =
      (fun ω => Complex.exp (-(t : ℂ)*symbol a ξ) *
        (phase a η s ω * phase a ξ t ω)) := by
    funext ω
    unfold normalized
    ring
  rw [he, integral_const_mul,
    MarkedTwoTimeHolomorphicTransform.two_time_transform a η ξ s t hst,
    ← Complex.exp_add]
  congr 1
  rw [NNReal.coe_sub hst]
  push_cast
  ring

theorem source_phase_integrable (a ξ η : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (MarkedExponentialTilt.source a ξ (fun _ => t)).Integrable (phase a η s) := by
  exact ComplexDensityUnbounded.integrable_density probability _
    (normalized_integrable a ξ t) _ ((phase_adapted a η s).measurable.mono
      ((history a).le s) le_rfl)
    (weighted_phase_integrable a ξ η s t hst)

theorem source_phase_transform (a ξ η : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ᵛ ω, phase a η s ω ∂[ContinuousLinearMap.mul ℝ ℂ;
      MarkedExponentialTilt.source a ξ (fun _ => t)]) =
      Complex.exp ((s : ℂ)*(symbol a (η+ξ)-symbol a ξ)) := by
  rw [MarkedExponentialTilt.source, ComplexDensityUnbounded.integral_density probability _
    (normalized_integrable a ξ t) _ ((phase_adapted a η s).measurable.mono
      ((history a).le s) le_rfl)
    (weighted_phase_integrable a ξ η s t hst)]
  exact weighted_phase_mean a ξ η s t hst

end OperatorDerivativeRewrite.Foundation.MarkedTiltTransform
