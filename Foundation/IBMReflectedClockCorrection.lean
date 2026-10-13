import Foundation.IBMConditionalOverlap

/-! Exact deterministic correction caused by reflection of the Brownian clock. -/
noncomputable section

namespace OperatorDerivativeRewrite.Foundation.IBMReflectedClockCorrection

/-- The loss in squared displacement when a clock is reflected at zero. -/
def crossingPenalty (x y : ℝ) : ℝ := 2 * (|x * y| - x * y)

/-- Reflection changes a squared increment only through the crossing term. -/
theorem reflected_increment_sq (x y : ℝ) :
    (|y| - |x|)^2 = (y - x)^2 - crossingPenalty x y := by
  unfold crossingPenalty
  rw [abs_mul]
  nlinarith [sq_abs x, sq_abs y]

/-- The correction is nonnegative and at most the unreflected squared increment. -/
theorem crossingPenalty_bounds (x y : ℝ) :
    0 ≤ crossingPenalty x y ∧ crossingPenalty x y ≤ (y - x)^2 := by
  constructor
  · unfold crossingPenalty
    have h := le_abs_self (x * y)
    linarith
  · have h := sq_nonneg (|y| - |x|)
    rw [reflected_increment_sq] at h
    linarith

/-- No crossing correction occurs when the endpoint product is nonnegative. -/
theorem crossingPenalty_eq_zero_of_nonneg {x y : ℝ} (h : 0 ≤ x * y) :
    crossingPenalty x y = 0 := by
  simp [crossingPenalty, abs_of_nonneg h]

/-- Opposite strict signs give the exact positive crossing correction. -/
theorem crossingPenalty_eq_of_neg {x y : ℝ} (h : x * y < 0) :
    crossingPenalty x y = -4 * (x * y) := by
  rw [crossingPenalty, abs_of_neg h]
  ring

/-- Crossing correction is supported precisely on opposite-sign endpoints. -/
theorem crossingPenalty_pos_iff (x y : ℝ) :
    0 < crossingPenalty x y ↔ x * y < 0 := by
  constructor
  · intro hp
    by_contra hn
    have h : 0 ≤ x * y := le_of_not_gt hn
    rw [crossingPenalty_eq_zero_of_nonneg h] at hp
    exact (lt_irrefl 0 hp)
  · intro h
    rw [crossingPenalty_eq_of_neg h]
    linarith

/-- The penalty is a bounded multiple of the endpoint product. -/
theorem crossingPenalty_le_abs_mul (x y : ℝ) :
    crossingPenalty x y ≤ 4 * |x * y| := by
  by_cases h : 0 ≤ x * y
  · rw [crossingPenalty_eq_zero_of_nonneg h]
    positivity
  · have hn : x * y < 0 := lt_of_not_ge h
    rw [crossingPenalty_eq_of_neg hn, abs_of_neg hn]
    linarith

end OperatorDerivativeRewrite.Foundation.IBMReflectedClockCorrection
