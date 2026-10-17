import Foundation.BandLimitedEntireCalculus
import Foundation.BandLimitedHeatLimit

/-! Genuine process expectation limits for all complex derivatives of admissible tests. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BandLimitedDifferentialHeatLimit
open BandLimitedComplexExtension BandLimitedEntireCalculus

theorem derivative_process_integrable (R : ℝ≥0) (φ : ℝ → ℂ)
    (hφ : Integrable φ (band R)) (k : ℕ) (t : ℝ≥0) (a : ℝ) :
    Integrable (fun ω => iteratedDeriv k (extension R φ)
      (MarkedRenewalMartingale.process a t ω)) MarkedRootRenewalProcess.probability := by
  rw [iterated_derivative_formula R φ hφ]
  exact process_integrable R _ (orderProfile_integrable R φ hφ k) t a

theorem derivative_expectation_limit (R : ℝ≥0) (φ : ℝ → ℂ)
    (hφ : Integrable φ (band R)) (k : ℕ) (T : ℝ≥0) (z : ℂ) :
    Tendsto (fun n : ℕ => ∫ ω, iteratedDeriv k (extension R φ)
      (z+MarkedRenewalMartingale.process (ComplexRootHeatTransformLimit.amplitude 1 n)
        ((n : ℝ≥0)*T) ω) ∂MarkedRootRenewalProcess.probability) atTop
      (𝓝 (∫ η, (orderProfile k φ η*Complex.exp (Complex.I*(η : ℂ)*z))*
        (Real.exp (-(T : ℝ)*η^4) : ℂ) ∂band R)) := by
  rw [iterated_derivative_formula R φ hφ]
  exact BandLimitedHeatLimit.starting_state_limit R _ (orderProfile_integrable R φ hφ k) T z

theorem fourth_expectation_limit (R : ℝ≥0) (φ : ℝ → ℂ)
    (hφ : Integrable φ (band R)) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ ω, iteratedDeriv 4 (extension R φ)
      (MarkedRenewalMartingale.process (ComplexRootHeatTransformLimit.amplitude 1 n)
        ((n : ℝ≥0)*T) ω) ∂MarkedRootRenewalProcess.probability) atTop
      (𝓝 (∫ η, (φ η*(η : ℂ)^4)*HigherHeatL2.symbol 2 T (η/(2*Real.pi)) ∂band R)) := by
  rw [fourth_derivative_formula R φ hφ]
  have hi : Integrable (fun η => φ η*(η : ℂ)^4) (band R) := by
    have he : orderProfile 4 φ = (fun η => φ η*(η : ℂ)^4) := by
      funext η
      simp [orderProfile, mul_pow, Complex.I_pow_four]
    rw [← he]
    exact orderProfile_integrable R φ hφ 4
  exact BandLimitedHeatLimit.operator_expectation_limit R _ hi T

end OperatorDerivativeRewrite.Foundation.BandLimitedDifferentialHeatLimit
