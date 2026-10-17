import Foundation.FourierPathTimeGradient
import Foundation.FourierPathControlTransfer

/-! Actual scalar time densities of realized Frechet derivatives and pseudo-expectation transfer. -/
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathTimeGradientRealization
open FourierPathBoundedControls BochnerTimeControlPairing FourierPathTimeGradient
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatFourierTranslations HigherHeatFourierPathSemigroup
open FourierPathDirectionalOperator HigherHeatInterpolatedPaths HigherHeatWeightedPaths

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def evaluation (ω : Path) : TestSpace levels ξ →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ ω).comp (realize levels ξ)

theorem evaluation_norm (ω : Path) : ‖evaluation levels ξ ω‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  simp only [one_mul]
  exact ((realize levels ξ q).norm_coe_le_norm ω).trans (realize_bound levels ξ q)

def realizedField (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (ω : Path) : BochnerTimeControlPairing.Field ℂ :=
  (evaluation levels ξ ω).compLpL 1 volume (timeGradient levels ξ m hm T hT q)

theorem realizedField_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (ω : Path) : ‖realizedField levels ξ m hm T hT q ω‖ ≤ (1+(T:ℝ)⁻¹)*‖q‖ := by
  calc
    _ ≤ ‖evaluation levels ξ ω‖*‖timeGradient levels ξ m hm T hT q‖ :=
      (evaluation levels ξ ω).norm_compLp_le _
    _ ≤ 1*((1+(T:ℝ)⁻¹)*‖q‖) := mul_le_mul (evaluation_norm levels ξ ω)
      (timeGradient_bound levels ξ m hm T hT q) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem realizedField_pairing (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (ω : Path) (u : Control) :
    pairing ℂ u (realizedField levels ξ m hm T hT q ω) =
      realize levels ξ (FourierPathControlGradient.gradient levels ξ m hm T hT q u) ω := by
  have hh := pairing_compLp ((evaluation levels ξ ω).restrictScalars ℝ) u
    (timeGradient levels ξ m hm T hT q)
  change pairing ℂ u (realizedField levels ξ m hm T hT q ω) =
    realize levels ξ (pairing (TestSpace levels ξ) u (timeGradient levels ξ m hm T hT q)) ω at hh
  rwa [timeGradient_pairing] at hh

theorem realized_hasFDerivAt (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (ω : Path) (u : Control) :
    HasFDerivAt (fun v => realize levels ξ (evolution levels ξ m hm T q) (addPath (direction v) ω))
      ((pairing ℂ).flip (realizedField levels ξ m hm T hT (translation levels ξ (direction u) q) ω)) u := by
  have hh := FourierPathControlFrechet.realized_hasFDerivAt levels ξ m hm T hT q ω u
  convert hh using 1
  ext v
  exact realizedField_pairing levels ξ m hm T hT _ ω v

theorem transfer_integral (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control) :
    (∫ s, u s • realizedField levels ξ m hm T hT q zeroPath s) =
      FourierPathControlTransfer.transfer levels ξ m hm T hT q u := by
  rw [← pairing_integral, realizedField_pairing]
  rfl

theorem expected_derivative_integral (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (u : Control) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ (direction u)) :
    expectation levels ξ m hm T hT z.2 = ∫ s, u s • realizedField levels ξ m hm T hT z.1 zeroPath s := by
  rw [transfer_integral]
  exact FourierPathControlTransfer.transfer_identity levels ξ m hm T hT u z hz

theorem weighted_density_limit (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (u : Control) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ (direction u)) :
    Tendsto (fun n => ∫ ω, pathWeight m hm T hT n ω • realize levels ξ z.2 ω
      ∂probabilityPath m hm T hT n) atTop
      (𝓝 (∫ s, u s • realizedField levels ξ m hm T hT z.1 zeroPath s)) := by
  rw [transfer_integral]
  exact FourierPathControlTransfer.weighted_transfer_limit levels ξ m hm T hT u z hz

end OperatorDerivativeRewrite.Foundation.FourierPathTimeGradientRealization
