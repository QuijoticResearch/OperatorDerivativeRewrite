import Foundation.ProbabilityTailBound

/-! Positive second-moment lower tail bounds on genuine finite probability spaces. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.FiniteProbabilityTailBound

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem finite_memLp (f : Ω → ℝ) (p : ℝ≥0∞) : MemLp f p μ := by
  classical
  apply MemLp.of_bound (measurable_of_countable f).aestronglyMeasurable (∑ x, ‖f x‖)
  exact Eventually.of_forall (fun x => Finset.single_le_sum
    (fun y _ => norm_nonneg (f y)) (Finset.mem_univ x))

theorem integral_mul_square_le (f g : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ)*(∫ x, (g x)^2 ∂μ) :=
  ProbabilityTailBound.integral_mul_square_le μ f g hf hg (finite_memLp μ f 2) (finite_memLp μ g 2)

theorem mean_tail_square (Y : Ω → ℝ) (hY : ∀ x, 0 ≤ Y x) (b : ℝ) (hb : 0 ≤ b)
    (hbm : b ≤ ∫ x, Y x ∂μ) :
    ((∫ x, Y x ∂μ)-b)^2 ≤ (∫ x, (Y x)^2 ∂μ)*μ.real {x | b < Y x} :=
  ProbabilityTailBound.mean_tail_square μ Y (measurable_of_countable Y) hY
    (finite_memLp μ Y 2) b hb hbm

end OperatorDerivativeRewrite.Foundation.FiniteProbabilityTailBound
