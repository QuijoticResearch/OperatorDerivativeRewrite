import Foundation.MarkedTwoTimeHolomorphicTransform
import Foundation.ComplexRootPoissonHeatLimit

/-! Fourth-order scaling of actual two-time complex-process holomorphic moments. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MarkedTwoTimeHeatLimit
open MarkedRootRenewalProcess (probability)
open MarkedHolomorphicExponential MarkedTwoTimeHolomorphicTransform
open ComplexRootHeatTransformLimit

theorem rate_scaled_factorization (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) (η ξ : ℝ) :
    (∫ ω, phase (amplitude 1 n) η ((n : ℝ≥0)*s) ω*
      phase (amplitude 1 n) ξ ((n : ℝ≥0)*t) ω ∂probability) =
      (∫ z : ℂ, Complex.exp (Complex.I*(η+ξ : ℝ)*z)
        ∂ComplexRootPoissonLaw.law ((n : ℝ≥0)*s) (amplitude 1 n))*
      (∫ z : ℂ, Complex.exp (Complex.I*(ξ : ℂ)*z)
        ∂ComplexRootPoissonLaw.law ((n : ℝ≥0)*(t-s)) (amplitude 1 n)) := by
  rw [two_time_transform _ η ξ _ _ (mul_le_mul_of_nonneg_left hst (zero_le : 0 ≤ (n : ℝ≥0))),
    ComplexRootPoissonTransform.transform,ComplexRootPoissonTransform.transform,
    ← Complex.exp_add,← mul_tsub]
  rfl

theorem rate_scaled_two_time_limit (s t : ℝ≥0) (hst : s ≤ t) (η ξ : ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, phase (amplitude 1 n) η ((n : ℝ≥0)*s) ω*
      phase (amplitude 1 n) ξ ((n : ℝ≥0)*t) ω ∂probability) atTop
      (𝓝 (((Real.exp (-(s : ℝ)*(η+ξ)^4) : ℝ) : ℂ)*
        ((Real.exp (-((t-s : ℝ≥0) : ℝ)*ξ^4) : ℝ) : ℂ))) := by
  have he := (ComplexRootPoissonHeatLimit.rate_scaled_transform_limit s (η+ξ)).mul
    (ComplexRootPoissonHeatLimit.rate_scaled_transform_limit (t-s) ξ)
  simpa only [← rate_scaled_factorization _ s t hst η ξ] using he

theorem rate_scaled_operator_two_time_limit (s t : ℝ≥0) (hst : s ≤ t) (η ξ : ℝ) :
    Tendsto (fun n : ℕ => ∫ ω,
      phase (amplitude 1 n) (2*Real.pi*η) ((n : ℝ≥0)*s) ω*
      phase (amplitude 1 n) (2*Real.pi*ξ) ((n : ℝ≥0)*t) ω ∂probability) atTop
      (𝓝 (HigherHeatL2.symbol 2 s (η+ξ)*HigherHeatL2.symbol 2 (t-s) ξ)) := by
  simpa only [HigherHeatL2.symbol,show 2*2=4 from rfl,← mul_add] using
    rate_scaled_two_time_limit s t hst (2*Real.pi*η) (2*Real.pi*ξ)

end OperatorDerivativeRewrite.Foundation.MarkedTwoTimeHeatLimit
