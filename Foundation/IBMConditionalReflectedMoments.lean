import Foundation.IBMReflectedClockCorrection

/-! Conditional IBM fourth moments with the exact zero-crossing correction. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace OperatorDerivativeRewrite.Foundation.IBMConditionalReflectedMoments
open InfiniteGaussian IBMSourceLaws IBMModificationBridge IBMContinuousComposition
open IBMConditionalIncrements IBMReflectedClockCorrection

variable (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
  (hS : ∀ ω, Continuous (fun r => S r ω))
  (hC : ∀ ω, Continuous (fun t => C t ω))

/-- Conditional fourth moment: unreflected Brownian-clock scale minus
exactly the zero-crossing penalty. -/
theorem conditional_increment_fourth_crossing
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (s t : ℝ≥0) (ωY : SampleSpace) :
    (∫ ωX, (value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY) -
      value (sceneryPath S hS) (clockPath C hC) s (ωX,ωY))^4
      ∂gaussianProduct) =
      3 * ((C t ωY - C s ωY)^2 - crossingPenalty (C s ωY) (C t ωY)) := by
  rw [conditional_increment_fourth S C hS hC hmodS]
  rw [sq_abs]
  rw [reflected_increment_sq]

/-- The unreflected clock increment gives a valid conditional upper bound,
with strict loss whenever the clock endpoints have opposite signs. -/
theorem conditional_increment_fourth_le
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (s t : ℝ≥0) (ωY : SampleSpace) :
    (∫ ωX, (value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY) -
      value (sceneryPath S hS) (clockPath C hC) s (ωX,ωY))^4
      ∂gaussianProduct) ≤ 3 * (C t ωY - C s ωY)^2 := by
  rw [conditional_increment_fourth_crossing S C hS hC hmodS]
  have h := (crossingPenalty_bounds (C s ωY) (C t ωY)).1
  linarith

/-- The conditional upper bound is exact when the clock does not change sign. -/
theorem conditional_increment_fourth_eq_of_same_sign
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (s t : ℝ≥0) (ωY : SampleSpace)
    (h : 0 ≤ C s ωY * C t ωY) :
    (∫ ωX, (value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY) -
      value (sceneryPath S hS) (clockPath C hC) s (ωX,ωY))^4
      ∂gaussianProduct) = 3 * (C t ωY - C s ωY)^2 := by
  rw [conditional_increment_fourth_crossing S C hS hC hmodS,
    crossingPenalty_eq_zero_of_nonneg h]
  ring

end OperatorDerivativeRewrite.Foundation.IBMConditionalReflectedMoments
