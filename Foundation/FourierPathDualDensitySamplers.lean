import Foundation.FourierPathDualDensityFubini

/-! Actual probability-path samplers, weighted time-density integrals and their verified limit. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualDensitySamplers
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathDualControls FourierPathDualDensityFubini FourierPathDualTimeGradient
open HigherHeatInterpolatedPaths HigherHeatWeightedPaths

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem sampler_joint_integrable (m : ℕ) [Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ) (u : Control m) (n : ℕ) :
    Integrable (weighted levels ξ m T hT q u (pathWeight k hk H hH n))
      (volume.prod (probabilityPath k hk H hH n)) := by
  letI := probabilityPath_isProbability k hk H hH n
  exact weighted_integrable levels ξ m T hT q u _ _ (pathWeight_integrable k hk H hH n)

theorem sampler_fubini (m : ℕ) [Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ) (u : Control m) (n : ℕ) :
    (∫ t : ℝ, ∫ ω, weighted levels ξ m T hT q u (pathWeight k hk H hH n) (t,ω)
      ∂probabilityPath k hk H hH n) =
      ∫ ω, pathWeight k hk H hH n ω •
        realize levels ξ (FourierPathDualGradient.gradient levels ξ m T hT q u) ω
          ∂probabilityPath k hk H hH n := by
  letI := probabilityPath_isProbability k hk H hH n
  exact weighted_fubini levels ξ m T hT q u _ _ (pathWeight_integrable k hk H hH n)

theorem sampler_density_limit (m : ℕ) [Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ) (u : Control m) :
    Tendsto (fun n => ∫ t : ℝ, ∫ ω,
      weighted levels ξ m T hT q u (pathWeight k hk H hH n) (t,ω)
        ∂probabilityPath k hk H hH n) atTop
      (𝓝 (∫ t : ℝ, u t • expectationField levels ξ m k hk T H hT hH q t)) := by
  have he : (fun n => ∫ t : ℝ, ∫ ω,
      weighted levels ξ m T hT q u (pathWeight k hk H hH n) (t,ω)
        ∂probabilityPath k hk H hH n) =
      (fun n => ∫ ω, pathWeight k hk H hH n ω •
        realize levels ξ (FourierPathDualGradient.gradient levels ξ m T hT q u) ω
          ∂probabilityPath k hk H hH n) :=
    funext (sampler_fubini levels ξ m k hk T H hT hH q u)
  rw [he, ← BochnerDualControlPairing.pairing_integral, expectationField_pairing]
  exact weighted_expectation_limit levels ξ k hk H hH _

end OperatorDerivativeRewrite.Foundation.FourierPathDualDensitySamplers
