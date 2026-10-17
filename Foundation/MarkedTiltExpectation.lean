import Foundation.MarkedExponentialTilt
import Foundation.ComplexDensityIntegral

/-! Actual path expectations for the normalized complex renewal laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MarkedTiltExpectation
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedExponentialMartingale MarkedUnboundedSampling
open MarkedExponentialTilt

variable (a ξ : ℝ) (τ : StateSample → ℝ≥0)
  (hτ : IsStoppingTime (history a) (fun ω => (τ ω : WithTop ℝ≥0)))
  (N : ℕ) (hN : ∀ ω, τ ω ≤ N)

include hτ hN in
theorem source_integrable (g : StateSample → ℂ) (hg : Measurable g)
    (C : ℝ) (hbound : ∀ ω, ‖g ω‖ ≤ C) : (source a ξ τ).Integrable g := by
  let := source_finite_variation a ξ τ hτ N hN
  exact Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hbound)

include hτ hN in
theorem source_integral (g : StateSample → ℂ) (hg : Measurable g)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ ω, ‖g ω‖ ≤ C) :
    (∫ᵛ ω, g ω ∂[ContinuousLinearMap.mul ℝ ℂ; source a ξ τ]) =
      ∫ ω, g ω * normalized a ξ (τ ω) ω ∂probability := by
  exact ComplexDensityIntegral.integral_density probability _
    (exponential_stopped_integrable a τ hτ N hN ξ) g hg C hC hbound

include hτ hN in
theorem law_integrable (g : RootRenewalPathLaw.Path → ℂ) (hg : Measurable g)
    (C : ℝ) (hbound : ∀ γ, ‖g γ‖ ≤ C) : (law a ξ τ).Integrable g := by
  let := law_finite_variation a ξ τ hτ N hN
  exact Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hbound)

include hτ hN in
theorem law_integral (g : RootRenewalPathLaw.Path → ℂ) (hg : Measurable g)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ γ, ‖g γ‖ ≤ C) :
    (∫ᵛ γ, g γ ∂[ContinuousLinearMap.mul ℝ ℂ; law a ξ τ]) =
      ∫ ω, g (RootRenewalPathLaw.path a ω) * normalized a ξ (τ ω) ω ∂probability := by
  rw [law, VectorMeasure.integral_map (RootRenewalPathLaw.path_measurable a)
    hg.aestronglyMeasurable
    (source_integrable a ξ τ hτ N hN _ (hg.comp (RootRenewalPathLaw.path_measurable a))
      C (fun ω => hbound _))]
  exact source_integral a ξ τ hτ N hN _
    (hg.comp (RootRenewalPathLaw.path_measurable a)) C hC (fun ω => hbound _)

end OperatorDerivativeRewrite.Foundation.MarkedTiltExpectation
