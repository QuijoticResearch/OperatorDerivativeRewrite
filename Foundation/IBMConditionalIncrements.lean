import Foundation.IBMConditionalFiniteDim
import Foundation.IBMSourceMoments

/-! Exact conditional fourth moments of IBM increments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMConditionalIncrements
open InfiniteGaussian IBMSourceLaws IBMModificationBridge IBMContinuousComposition
open IBMSourceMoments

variable (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
  (hS : ∀ ω, Continuous (fun r => S r ω))
  (hC : ∀ ω, Continuous (fun t => C t ω))

/-- The actual Brownian scenery fourth-increment identity transfers to the
composed path for every fixed clock sample. -/
theorem conditional_increment_fourth
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (s t : ℝ≥0) (ωY : SampleSpace) :
    (∫ ωX, (value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY) -
      value (sceneryPath S hS) (clockPath C hC) s (ωX,ωY))^4
      ∂gaussianProduct) =
      3 * abs (|C t ωY| - |C s ωY|)^2 := by
  have ht := hmodS |C t ωY|
  have hs := hmodS |C s ωY|
  have he : (fun ωX => (value (sceneryPath S hS) (clockPath C hC) t
        (ωX,ωY) - value (sceneryPath S hS) (clockPath C hC) s
        (ωX,ωY))^4) =ᵐ[gaussianProduct]
      (fun ωX => (sceneryBase |C t ωY| ωX - sceneryBase |C s ωY| ωX)^4) := by
    filter_upwards [ht, hs] with ωX hxt hxs
    simp only [value_eq, sceneryPath_apply, clockPath_apply, hxt, hxs]
  rw [integral_congr_ae he, sceneryBase_increment_fourth]

end OperatorDerivativeRewrite.Foundation.IBMConditionalIncrements
