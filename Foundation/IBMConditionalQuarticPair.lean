import Foundation.IBMSceneryQuarticPair
import Foundation.IBMConditionalOverlap

/-! Conditional mixed fourth-power moment of two IBM increments. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace OperatorDerivativeRewrite.Foundation.IBMConditionalQuarticPair
open InfiniteGaussian IBMSourceLaws IBMModificationBridge IBMContinuousComposition
open IBMSceneryQuarticPair IBMSpatialOverlap

variable (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
  (hS : ∀ ω, Continuous (fun r => S r ω))
  (hC : ∀ ω, Continuous (fun t => C t ω))

/-- For a fixed clock sample, the fourth-power product of two IBM
increments has the exact Wick polynomial with their signed spatial overlap. -/
theorem conditional_increment_fourth_product
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (s t u v : ℝ≥0) (ωY : SampleSpace) :
    (∫ ωX,
      (value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY) -
        value (sceneryPath S hS) (clockPath C hC) s (ωX,ωY))^4 *
      (value (sceneryPath S hS) (clockPath C hC) v (ωX,ωY) -
        value (sceneryPath S hS) (clockPath C hC) u (ωX,ωY))^4
      ∂gaussianProduct) =
      9 * (|C t ωY| - |C s ωY|)^2 * (|C v ωY| - |C u ωY|)^2 +
      72 * abs (|C t ωY| - |C s ωY|) *
        abs (|C v ωY| - |C u ωY|) *
        (signedOverlap |C s ωY| |C t ωY| |C u ωY| |C v ωY|)^2 +
      24 * (signedOverlap |C s ωY| |C t ωY| |C u ωY| |C v ωY|)^4 := by
  have he : (fun ωX =>
      (value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY) -
        value (sceneryPath S hS) (clockPath C hC) s (ωX,ωY))^4 *
      (value (sceneryPath S hS) (clockPath C hC) v (ωX,ωY) -
        value (sceneryPath S hS) (clockPath C hC) u (ωX,ωY))^4) =ᵐ[gaussianProduct]
      (fun ωX =>
        (sceneryBase |C t ωY| ωX - sceneryBase |C s ωY| ωX)^4 *
        (sceneryBase |C v ωY| ωX - sceneryBase |C u ωY| ωX)^4) := by
    filter_upwards [hmodS |C t ωY|, hmodS |C s ωY|,
      hmodS |C v ωY|, hmodS |C u ωY|] with ωX ht hs hv hu
    simp only [value_eq, sceneryPath_apply, clockPath_apply, ht, hs, hv, hu]
  rw [integral_congr_ae he,
    scenery_increment_fourth_product |C s ωY| |C t ωY| |C u ωY| |C v ωY|
      (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)]
  simp only [sq_abs]


/-- Fourth power of one supplied-path IBM increment, as a scenery
random variable after the clock sample has been fixed. -/
def fourthPower (s t : ℝ≥0) (ωY : SampleSpace) (ωX : SampleSpace) : ℝ :=
  (value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY) -
    value (sceneryPath S hS) (clockPath C hC) s (ωX,ωY))^4

/-- Exact conditional centered product of two fourth-power increments.
All additional correlation from shared scenery is nonnegative and is
controlled by the squared and fourth powers of signed spatial overlap. -/
theorem conditional_fourth_centered_product
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (s t u v : ℝ≥0) (ωY : SampleSpace) :
    (∫ ωX, fourthPower S C hS hC s t ωY ωX *
      fourthPower S C hS hC u v ωY ωX ∂gaussianProduct) -
      (∫ ωX, fourthPower S C hS hC s t ωY ωX ∂gaussianProduct) *
      (∫ ωX, fourthPower S C hS hC u v ωY ωX ∂gaussianProduct) =
      72 * abs (|C t ωY| - |C s ωY|) *
        abs (|C v ωY| - |C u ωY|) *
        (signedOverlap |C s ωY| |C t ωY| |C u ωY| |C v ωY|)^2 +
      24 * (signedOverlap |C s ωY| |C t ωY| |C u ωY| |C v ωY|)^4 := by
  change (∫ ωX,
      (value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY) -
        value (sceneryPath S hS) (clockPath C hC) s (ωX,ωY))^4 *
      (value (sceneryPath S hS) (clockPath C hC) v (ωX,ωY) -
        value (sceneryPath S hS) (clockPath C hC) u (ωX,ωY))^4 ∂gaussianProduct) -
      (∫ ωX, (value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY) -
        value (sceneryPath S hS) (clockPath C hC) s (ωX,ωY))^4 ∂gaussianProduct) *
      (∫ ωX, (value (sceneryPath S hS) (clockPath C hC) v (ωX,ωY) -
        value (sceneryPath S hS) (clockPath C hC) u (ωX,ωY))^4 ∂gaussianProduct) = _
  rw [conditional_increment_fourth_product S C hS hC hmodS,
    IBMConditionalIncrements.conditional_increment_fourth S C hS hC hmodS s t ωY,
    IBMConditionalIncrements.conditional_increment_fourth S C hS hC hmodS u v ωY]
  simp only [sq_abs]
  ring
end OperatorDerivativeRewrite.Foundation.IBMConditionalQuarticPair
