import Foundation.FourierPathHeatTransfer
import Foundation.FourierPathDirectionalAdjoint

/-! Actual adjoint values and signed/weighted path realization of positive transfer results. -/
noncomputable section
open Filter MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathPositiveTransferRealization
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatFourierTranslations HigherHeatInterpolatedPaths HigherHeatWeightedPaths
open FourierPathDirectionalOperator FourierPathHeatTransfer

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def expectationComponent (part : ℂ →L[ℝ] ℝ) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) : StrongDual ℝ (TestSpace levels ξ) :=
  part.comp ((expectation levels ξ m hm T hT).restrictScalars ℝ)

def transferComponent (part : ℂ →L[ℝ] ℝ) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) : StrongDual ℝ (TestSpace levels ξ) :=
  part.comp ((linearTransfer levels ξ m hm T hT).restrictScalars ℝ)

theorem component_adjoint_graph (part : ℂ →L[ℝ] ℝ) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) :
    (expectationComponent levels ξ part m hm T hT,transferComponent levels ξ part m hm T hT) ∈
      (FourierPathDirectionalAdjoint.adjoint levels ξ FourierPathLinearDirection.direction).graph := by
  apply (FourierPathDirectionalAdjoint.adjoint_graph_pairing levels ξ _ _ _).mpr
  intro z hz
  change part (linearTransfer levels ξ m hm T hT z.1)=part (expectation levels ξ m hm T hT z.2)
  rw [linearTransfer_identity levels ξ m hm T hT z hz]

theorem component_in_adjoint_domain (part : ℂ →L[ℝ] ℝ) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) :
    expectationComponent levels ξ part m hm T hT ∈
      (FourierPathDirectionalAdjoint.adjoint levels ξ FourierPathLinearDirection.direction).domain := by
  apply LinearPMap.mem_domain_iff.mpr
  exact ⟨transferComponent levels ξ part m hm T hT,component_adjoint_graph levels ξ part m hm T hT⟩

theorem component_adjoint_apply (part : ℂ →L[ℝ] ℝ) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) :
    FourierPathDirectionalAdjoint.adjoint levels ξ FourierPathLinearDirection.direction
      ⟨expectationComponent levels ξ part m hm T hT,
        component_in_adjoint_domain levels ξ part m hm T hT⟩=
      transferComponent levels ξ part m hm T hT := by
  exact (FourierPathDirectionalAdjoint.adjoint levels ξ _).mem_graph_snd_inj
    ((FourierPathDirectionalAdjoint.adjoint levels ξ _).mem_graph
      ⟨expectationComponent levels ξ part m hm T hT,
        component_in_adjoint_domain levels ξ part m hm T hT⟩)
    (component_adjoint_graph levels ξ part m hm T hT) rfl

theorem signed_transfer_limit (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ FourierPathLinearDirection.direction) :
    Tendsto (fun n => ∫ᵛ ω, realize levels ξ z.2 ω ∂<•signedPath m hm T hT n)
      atTop (𝓝 (linearTransfer levels ξ m hm T hT z.1)) := by
  have ht := expectation_limit levels ξ m hm T hT z.2
  rwa [linearTransfer_identity levels ξ m hm T hT z hz] at ht

theorem weighted_transfer_limit (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ FourierPathLinearDirection.direction) :
    Tendsto (fun n => ∫ ω, pathWeight m hm T hT n ω • realize levels ξ z.2 ω
      ∂probabilityPath m hm T hT n) atTop (𝓝 (linearTransfer levels ξ m hm T hT z.1)) := by
  have ht := weighted_expectation_limit levels ξ m hm T hT z.2
  rwa [linearTransfer_identity levels ξ m hm T hT z hz] at ht

theorem realized_graph_derivative (ω : Path) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ FourierPathLinearDirection.direction) :
    HasDerivAt (fun t => realize levels ξ z.1
      (addPath (scalePath t FourierPathLinearDirection.direction) ω)) (realize levels ξ z.2 ω) 0 := by
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := hz
  exact FourierPathDirectionalSeries.realized_hasDerivAt levels ξ _ ω a b hab

end OperatorDerivativeRewrite.Foundation.FourierPathPositiveTransferRealization
