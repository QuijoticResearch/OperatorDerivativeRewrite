import Foundation.FourierPathControlGradient
import Foundation.FourierPathPositiveTransferRealization

/-! Actual bounded control-dual transfer, adjoint values and stochastic approximant limits. -/
noncomputable section
open Filter MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathControlTransfer
open FourierPathBoundedControls HigherHeatDyadicLaws HigherHeatContinuousCylinders
open HigherHeatFourierBanach HigherHeatFourierTranslations HigherHeatFourierPathSemigroup
open FourierPathDirectionalOperator FourierPathPositiveTransferRealization
open HigherHeatInterpolatedPaths HigherHeatWeightedPaths

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def evaluation : TestSpace levels ξ →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ zeroPath).comp (realize levels ξ)

theorem evaluation_bound (q : TestSpace levels ξ) : ‖evaluation levels ξ q‖ ≤ ‖q‖ :=
  ((realize levels ξ q).norm_coe_le_norm zeroPath).trans (realize_bound levels ξ q)

def transfer (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    TestSpace levels ξ →L[ℂ] (Control →L[ℝ] ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun q => ((evaluation levels ξ).restrictScalars ℝ).comp
        (FourierPathControlGradient.gradient levels ξ m hm T hT q)
      map_add' := by intro q r; ext u; simp
      map_smul' := by intro c q; ext u; simp }
    (1+(T:ℝ)⁻¹) (fun q => by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro u
      exact (evaluation_bound levels ξ _).trans
        (FourierPathControlGradient.bilinear_bound levels ξ m hm T hT q u))

theorem transfer_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ‖transfer levels ξ m hm T hT‖ ≤ 1+(T:ℝ)⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

theorem bilinear_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control) :
    ‖transfer levels ξ m hm T hT q u‖ ≤ (1+(T:ℝ)⁻¹)*‖q‖*‖u‖ :=
  (transfer levels ξ m hm T hT q).le_of_opNorm_le
    ((transfer levels ξ m hm T hT).le_of_opNorm_le (transfer_bound levels ξ m hm T hT) q) u

def transferAt (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u : Control) :
    TestSpace levels ξ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun q => transfer levels ξ m hm T hT q u
      map_add' := by intro q r; simp
      map_smul' := by intro c q; simp }
    ((1+(T:ℝ)⁻¹)*‖u‖) (fun q => by
      exact (bilinear_bound levels ξ m hm T hT q u).trans_eq (by ring))

theorem transfer_identity (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (u : Control) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ (direction u)) :
    expectation levels ξ m hm T hT z.2 = transfer levels ξ m hm T hT z.1 u := by
  have hs := FourierPathDifferentialCommutation.heat_graph levels ξ (direction u) m hm T z hz
  have hg := FourierPathControlGradient.gradient_graph levels ξ m hm T hT z.1 u
  have hs' : (evolution levels ξ m hm T z.1, evolution levels ξ m hm T z.2) ∈
      (operator levels ξ (direction u)).graph := by rw [operator_graph]; exact hs
  have hg' : (evolution levels ξ m hm T z.1,
      FourierPathControlGradient.gradient levels ξ m hm T hT z.1 u) ∈
      (operator levels ξ (direction u)).graph := by rw [operator_graph]; exact hg
  have hv := (operator levels ξ (direction u)).mem_graph_snd_inj hs' hg' rfl
  rw [← expectation_at_zero levels ξ m hm T hT z.2, hv]
  rfl

theorem component_adjoint_graph (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (u : Control) (part : ℂ →L[ℝ] ℝ) :
    (expectationComponent levels ξ part m hm T hT,
      part.comp ((transferAt levels ξ m hm T hT u).restrictScalars ℝ)) ∈
      (FourierPathDirectionalAdjoint.adjoint levels ξ (direction u)).graph := by
  apply (FourierPathDirectionalAdjoint.adjoint_graph_pairing levels ξ (direction u) _ _).mpr
  intro z hz
  change part (transfer levels ξ m hm T hT z.1 u) = part (expectation levels ξ m hm T hT z.2)
  rw [transfer_identity levels ξ m hm T hT u z hz]

theorem signed_transfer_limit (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (u : Control) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ (direction u)) :
    Tendsto (fun n => ∫ᵛ ω, realize levels ξ z.2 ω ∂<•signedPath m hm T hT n)
      atTop (𝓝 (transfer levels ξ m hm T hT z.1 u)) := by
  have ht := expectation_limit levels ξ m hm T hT z.2
  rwa [transfer_identity levels ξ m hm T hT u z hz] at ht

theorem weighted_transfer_limit (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (u : Control) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ (direction u)) :
    Tendsto (fun n => ∫ ω, pathWeight m hm T hT n ω • realize levels ξ z.2 ω
      ∂probabilityPath m hm T hT n) atTop (𝓝 (transfer levels ξ m hm T hT z.1 u)) := by
  have ht := weighted_expectation_limit levels ξ m hm T hT z.2
  rwa [transfer_identity levels ξ m hm T hT u z hz] at ht

end OperatorDerivativeRewrite.Foundation.FourierPathControlTransfer
