import Foundation.ComplexDensityUnbounded

/-! Pushforward of integrable complex densities, as equality of actual vector measures. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.ComplexDensityPushforward

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

theorem map_density (μ : Measure Ω) (X : Ω → S) (hX : Measurable X)
    (ρ : S → ℂ) (hρ : Measurable ρ) (hi : Integrable ρ (μ.map X)) :
    (μ.withDensityᵥ (fun ω => ρ (X ω))).map X = (μ.map X).withDensityᵥ ρ := by
  have hs : Integrable (fun ω => ρ (X ω)) μ :=
    (integrable_map_measure hρ.aestronglyMeasurable hX.aemeasurable).mp hi
  apply VectorMeasure.ext
  intro A hA
  rw [VectorMeasure.map_apply _ hX hA, withDensityᵥ_apply hs (hX hA),
    withDensityᵥ_apply hi hA, setIntegral_map hA hρ.aestronglyMeasurable hX.aemeasurable]

end OperatorDerivativeRewrite.Foundation.ComplexDensityPushforward
