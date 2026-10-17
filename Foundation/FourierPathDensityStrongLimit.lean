import Foundation.FourierPathSamplerOperators
import Foundation.LpStrongOperatorConvergence

/-! Strong Bochner convergence of actual weighted probability-sampler time densities. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDensityStrongLimit
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathDualControls FourierPathDualTimeGradient FourierPathDualJointDensity
open HigherHeatInterpolatedPaths HigherHeatWeightedPaths FourierPathSamplerOperators

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def sampledField (m : ℕ) [Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (n : ℕ) (q : TestSpace levels ξ) :
    BochnerDualControlPairing.Field ℂ m :=
  (finite levels ξ k hk H hH n).compLpL (HigherHeatLpControls.power m) volume
    (timeGradient levels ξ m T hT q)

theorem sampledField_bound (m : ℕ) [Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (n : ℕ) (q : TestSpace levels ξ) :
    ‖sampledField levels ξ m k hk T H hT hH n q‖ ≤ (1+(T : ℝ)⁻¹)*‖q‖ := by
  calc
    _ ≤ ‖finite levels ξ k hk H hH n‖ * ‖timeGradient levels ξ m T hT q‖ :=
      (finite levels ξ k hk H hH n).norm_compLp_le _
    _ ≤ 1*((1+(T : ℝ)⁻¹)*‖q‖) := mul_le_mul (finite_norm levels ξ k hk H hH n)
      (timeGradient_bound levels ξ m T hT q) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem sampledField_ae (m : ℕ) [Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (n : ℕ) (q : TestSpace levels ξ) :
    (sampledField levels ξ m k hk T H hT hH n q : ℝ → ℂ) =ᵐ[volume]
      fun t => ∫ ω, pathWeight k hk H hH n ω • joint levels ξ m T hT q (t,ω)
        ∂probabilityPath k hk H hH n := by
  filter_upwards [(finite levels ξ k hk H hH n).coeFn_compLpL (timeGradient levels ξ m T hT q),
    representative_ae levels ξ m T hT q] with t ht hr
  exact ht.trans ((congrArg (finite levels ξ k hk H hH n) hr).trans
    (finite_apply levels ξ k hk H hH n (representative levels ξ m T hT q t)))

theorem expectationField_ae (m : ℕ) [Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ) :
    (expectationField levels ξ m k hk T H hT hH q : ℝ → ℂ) =ᵐ[volume]
      fun t => expectation levels ξ k hk H hH (representative levels ξ m T hT q t) := by
  filter_upwards [(expectation levels ξ k hk H hH).coeFn_compLpL (timeGradient levels ξ m T hT q),
    representative_ae levels ξ m T hT q] with t ht hr
  exact ht.trans (congrArg (expectation levels ξ k hk H hH) hr)

theorem sampledField_tendsto (m : ℕ) [Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ) :
    Tendsto (fun n => sampledField levels ξ m k hk T H hT hH n q) atTop
      (𝓝 (expectationField levels ξ m k hk T H hT hH q)) :=
  LpStrongOperatorConvergence.compLp_tendsto (volume : Measure ℝ) m
    (finite levels ξ k hk H hH) (expectation levels ξ k hk H hH)
    (finite_norm levels ξ k hk H hH) (expectation_norm levels ξ k hk H hH).le
    (finite_tendsto levels ξ k hk H hH) (timeGradient levels ξ m T hT q)

theorem section_tendsto (m : ℕ) [Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ) (t : ℝ) :
    Tendsto (fun n => ∫ ω, pathWeight k hk H hH n ω • joint levels ξ m T hT q (t,ω)
      ∂probabilityPath k hk H hH n) atTop
      (𝓝 (expectation levels ξ k hk H hH (representative levels ξ m T hT q t))) := by
  have ht := finite_tendsto levels ξ k hk H hH (representative levels ξ m T hT q t)
  simpa only [finite_apply, joint] using ht

theorem sampledField_contraction (m : ℕ) [Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (n : ℕ) (q : TestSpace levels ξ) (u : Control m) :
    BochnerDualControlPairing.pairing ℂ m u (sampledField levels ξ m k hk T H hT hH n q) =
      ∫ ω, pathWeight k hk H hH n ω •
        realize levels ξ (FourierPathDualGradient.gradient levels ξ m T hT q u) ω
          ∂probabilityPath k hk H hH n := by
  have hh := BochnerDualControlPairing.pairing_compLp (TestSpace levels ξ) m
    ((finite levels ξ k hk H hH n).restrictScalars ℝ) u (timeGradient levels ξ m T hT q)
  change BochnerDualControlPairing.pairing ℂ m u (sampledField levels ξ m k hk T H hT hH n q) =
    finite levels ξ k hk H hH n
      (BochnerDualControlPairing.pairing (TestSpace levels ξ) m u (timeGradient levels ξ m T hT q)) at hh
  rw [timeGradient_pairing, finite_apply] at hh
  exact hh

theorem contraction_operator_tendsto (m : ℕ) [Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ) :
    Tendsto (fun n => (BochnerDualControlPairing.pairing ℂ m).flip
      (sampledField levels ξ m k hk T H hT hH n q)) atTop
      (𝓝 ((BochnerDualControlPairing.pairing ℂ m).flip
        (expectationField levels ξ m k hk T H hT hH q))) :=
  (BochnerDualControlPairing.pairing ℂ m).flip.continuous.continuousAt.tendsto.comp
    (sampledField_tendsto levels ξ m k hk T H hT hH q)

end OperatorDerivativeRewrite.Foundation.FourierPathDensityStrongLimit
