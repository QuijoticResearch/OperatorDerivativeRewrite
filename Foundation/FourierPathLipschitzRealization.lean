import Foundation.FourierPathLipschitzTransfer
import Foundation.FourierPathPositiveTransferRealization
import Foundation.FourierPathRoughAdjointObstruction

/-! Actual directional adjoint values and stochastic limits for local Lipschitz directions. -/
noncomputable section
open Filter MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathLipschitzRealization
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatInterpolatedPaths HigherHeatWeightedPaths FourierPathDirectionalOperator
open FourierPathLipschitzTransfer FourierPathPositiveTransferRealization

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def transferComponent (h : Path) (K : ℝ≥0) (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (part : ℂ →L[ℝ] ℝ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    StrongDual ℝ (TestSpace levels ξ) :=
  part.comp ((transfer levels ξ h K hK m hm T hT).restrictScalars ℝ)

theorem component_adjoint_graph (h : Path) (K : ℝ≥0)
    (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (part : ℂ →L[ℝ] ℝ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    (expectationComponent levels ξ part m hm T hT,
      transferComponent levels ξ h K hK part m hm T hT) ∈
      (FourierPathDirectionalAdjoint.adjoint levels ξ h).graph := by
  apply (FourierPathDirectionalAdjoint.adjoint_graph_pairing levels ξ h _ _).mpr
  intro z hz
  change part (transfer levels ξ h K hK m hm T hT z.1)=part (expectation levels ξ m hm T hT z.2)
  rw [transfer_identity levels ξ h K hK m hm T hT z hz]

theorem component_in_adjoint_domain (h : Path) (K : ℝ≥0)
    (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (part : ℂ →L[ℝ] ℝ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    expectationComponent levels ξ part m hm T hT ∈ (FourierPathDirectionalAdjoint.adjoint levels ξ h).domain := by
  apply LinearPMap.mem_domain_iff.mpr
  exact ⟨transferComponent levels ξ h K hK part m hm T hT,
    component_adjoint_graph levels ξ h K hK part m hm T hT⟩

theorem component_adjoint_apply (h : Path) (K : ℝ≥0)
    (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (part : ℂ →L[ℝ] ℝ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    FourierPathDirectionalAdjoint.adjoint levels ξ h
      ⟨expectationComponent levels ξ part m hm T hT,
        component_in_adjoint_domain levels ξ h K hK part m hm T hT⟩=
      transferComponent levels ξ h K hK part m hm T hT := by
  exact (FourierPathDirectionalAdjoint.adjoint levels ξ h).mem_graph_snd_inj
    ((FourierPathDirectionalAdjoint.adjoint levels ξ h).mem_graph
      ⟨expectationComponent levels ξ part m hm T hT,
        component_in_adjoint_domain levels ξ h K hK part m hm T hT⟩)
    (component_adjoint_graph levels ξ h K hK part m hm T hT) rfl

theorem signed_transfer_limit (h : Path) (K : ℝ≥0)
    (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (z : TestSpace levels ξ × TestSpace levels ξ) (hz : z ∈ graph levels ξ h) :
    Tendsto (fun n => ∫ᵛ ω, realize levels ξ z.2 ω ∂<•signedPath m hm T hT n) atTop
      (𝓝 (transfer levels ξ h K hK m hm T hT z.1)) := by
  have ht := expectation_limit levels ξ m hm T hT z.2
  rwa [transfer_identity levels ξ h K hK m hm T hT z hz] at ht

theorem weighted_transfer_limit (h : Path) (K : ℝ≥0)
    (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (z : TestSpace levels ξ × TestSpace levels ξ) (hz : z ∈ graph levels ξ h) :
    Tendsto (fun n => ∫ ω, pathWeight m hm T hT n ω • realize levels ξ z.2 ω
      ∂probabilityPath m hm T hT n) atTop (𝓝 (transfer levels ξ h K hK m hm T hT z.1)) := by
  have ht := weighted_expectation_limit levels ξ m hm T hT z.2
  rwa [transfer_identity levels ξ h K hK m hm T hT z hz] at ht

theorem rough_direction_not_lipschitz (K : ℝ≥0) :
    ¬ LipschitzOnWith K FourierPathRoughDirection.direction.val (Set.Icc (0:ℝ) 1) := by
  intro hK
  have hp := component_in_adjoint_domain FourierPathRoughDirection.levels
    FourierPathRoughDirection.frequencies FourierPathRoughDirection.direction K hK
    Complex.imCLM 2 (by norm_num) 1 (by norm_num)
  exact FourierPathRoughAdjointObstruction.expectation_not_in_adjoint_domain 1 (by norm_num) hp

end OperatorDerivativeRewrite.Foundation.FourierPathLipschitzRealization
