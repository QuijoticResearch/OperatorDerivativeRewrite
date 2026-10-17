import Foundation.MarkedTiltTransform
import Foundation.ComplexRootPoissonHeatLimit

/-! Actual complex tilted expectations converge to a shifted fourth-order heat multiplier. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MarkedTiltHeatLimit
open MarkedRootRenewalProcess (probability)
open MarkedHolomorphicExponential MarkedTiltTransform ComplexRootHeatTransformLimit

theorem source_transform_ratio (a ξ η : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ᵛ ω, phase a η s ω ∂[ContinuousLinearMap.mul ℝ ℂ;
      MarkedExponentialTilt.source a ξ (fun _ => t)]) =
      (∫ z : ℂ, Complex.exp (Complex.I*((η+ξ : ℝ) : ℂ)*z)
        ∂ComplexRootPoissonLaw.law s a) /
      (∫ z : ℂ, Complex.exp (Complex.I*(ξ : ℂ)*z)
        ∂ComplexRootPoissonLaw.law s a) := by
  rw [source_phase_transform a ξ η s t hst,
    ComplexRootPoissonTransform.transform, ComplexRootPoissonTransform.transform,
    ← Complex.exp_sub]
  congr 1
  unfold symbol
  ring

theorem rate_scaled_tilt_limit (s t : ℝ≥0) (hst : s ≤ t) (ξ η : ℝ) :
    Tendsto (fun n : ℕ => ∫ᵛ ω, phase (amplitude 1 n) η ((n : ℝ≥0)*s) ω
      ∂[ContinuousLinearMap.mul ℝ ℂ;
        MarkedExponentialTilt.source (amplitude 1 n) ξ (fun _ => (n : ℝ≥0)*t)]) atTop
      (𝓝 ((Real.exp (-(s : ℝ)*((η+ξ)^4-ξ^4)) : ℝ) : ℂ)) := by
  have hn : (((Real.exp (-(s : ℝ)*ξ^4) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
  have ht := (ComplexRootPoissonHeatLimit.rate_scaled_transform_limit s (η+ξ)).div
    (ComplexRootPoissonHeatLimit.rate_scaled_transform_limit s ξ) hn
  have he : (((Real.exp (-(s : ℝ)*(η+ξ)^4) : ℝ) : ℂ) /
      ((Real.exp (-(s : ℝ)*ξ^4) : ℝ) : ℂ)) =
      ((Real.exp (-(s : ℝ)*((η+ξ)^4-ξ^4)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_div, ← Real.exp_sub]
    congr 2
    ring
  rw [he] at ht
  convert ht using 1
  funext n
  exact source_transform_ratio _ ξ η _ _
    (mul_le_mul_of_nonneg_left hst (zero_le : 0 ≤ (n : ℝ≥0)))

end OperatorDerivativeRewrite.Foundation.MarkedTiltHeatLimit
