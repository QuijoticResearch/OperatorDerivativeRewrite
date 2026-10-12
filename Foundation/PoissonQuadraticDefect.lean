import Foundation.PoissonLipschitzChain

/-! A genuine weighted-L² quadratic jump defect on the bounded scalar core. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.PoissonQuadraticDefect
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonCoordinateEvaluation PoissonBoundedCalculus PoissonMultipliers

/-- The quadratic finite-difference defect is the square of the actual
maximal difference, as an equality of rate-weighted field L² classes. -/
theorem bounded_square_difference (rate : ℝ≥0) (hr : 0 < rate)
    (f : ℕ → ℝ) (C : ℝ) (hf : ∀ n, |f n| ≤ C) :
    (maximalDifference rate hr)
      ⟨scalarOfBounded rate (fun n => f n * f n) (C * C)
        (bounded_mul f f C C hf hf),
        bounded_product_mem_maximalDifference rate hr f f C C hf hf⟩ =
      (2 : ℝ) • fieldMul rate (boundedDifference rate hr f C hf) f C hf +
      fieldMul rate (boundedDifference rate hr f C hf)
        (fun n => (boundedDifference rate hr f C hf) n) (2 * C)
        (boundedDifference_bound rate hr f C hf) := by
  apply Lp.ext
  filter_upwards [] with n
  rw [field_add_apply rate hr, field_smul_apply rate hr,
    fieldMul_apply rate hr, fieldMul_apply rate hr,
    bounded_difference_apply rate hr (fun n => f n * f n)
      (C * C) (bounded_mul f f C C hf hf) n,
    boundedDifference_apply rate hr]
  ring

end OperatorDerivativeRewrite.Foundation.PoissonQuadraticDefect

