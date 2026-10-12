import Foundation.L2ZeroExtension
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! The closed L2 subspace of classes supported in a measurable set. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s : Set Ω}

def supportedL2 (hs : MeasurableSet s) : Submodule ℝ (Lp ℝ 2 μ) :=
  (L2ZeroExtensionIsometry (μ := μ) hs).toLinearMap.range

theorem supportedL2_isClosed (hs : MeasurableSet s) :
    IsClosed (supportedL2 (μ := μ) hs : Set (Lp ℝ 2 μ)) :=
  (L2ZeroExtensionIsometry hs).isometry.isClosedEmbedding.isClosed_range

theorem mem_supportedL2_iff (hs : MeasurableSet s) (F : Lp ℝ 2 μ) :
    F ∈ supportedL2 hs ↔ ∀ᵐ x ∂μ, x ∉ s → F x = 0 := by
  constructor
  · rintro ⟨G, rfl⟩
    filter_upwards [L2ZeroExtension_coeFn hs G] with x hx hxs
    change L2ZeroExtension hs G x = 0
    rw [hx, indicator_of_notMem hxs]
  · intro hf
    let R : Lp ℝ 2 (μ.restrict s) := ((Lp.memLp F).restrict s).toLp F
    refine ⟨R, ?_⟩
    apply Lp.ext
    have hr := (ae_eq_restrict_iff_indicator_ae_eq hs).mp
      (show R =ᵐ[μ.restrict s] F from MemLp.coeFn_toLp _)
    filter_upwards [L2ZeroExtension_coeFn hs R, hr, hf] with x he hr hf
    change L2ZeroExtension hs R x = F x
    rw [he, hr]
    by_cases hx : x ∈ s
    · simp [hx]
    · simp [hx, hf hx]

end OperatorDerivativeRewrite.Foundation
