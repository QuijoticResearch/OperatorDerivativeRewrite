import Foundation.IBMConditionalMixture
import Foundation.GaussianBrownianBracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Probability bounds rule out the growing cosine mode of an unforced positive
biharmonic generator. This is a necessary-mode diagnostic, not a PDE uniqueness theorem. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.ManuscriptGeneratorDiagnostics

theorem cosine_expectation_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (k : ℝ) :
    (∫ ω, Real.cos (k * X ω) ∂μ) ≤ 1 := by
  have hm : AEStronglyMeasurable (fun ω => Real.cos (k * X ω)) μ :=
    (Real.continuous_cos.measurable.comp (measurable_const.mul hX)).aestronglyMeasurable
  have hi : Integrable (fun ω => Real.cos (k * X ω)) μ :=
    (integrable_const (1 : ℝ)).mono' hm (Filter.Eventually.of_forall (fun ω =>
      by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (k * X ω)))
  have h := integral_mono hi (integrable_const (1 : ℝ))
    (fun ω => Real.cos_le_one (k * X ω))
  simpa using h

/-- The Fourier multiplier exp(t k⁴/8) cannot be an expectation of a cosine. -/
theorem growing_biharmonic_cosine_impossible {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (k t : ℝ) (hk : k ≠ 0) (ht : 0 < t) :
    (∫ ω, Real.cos (k * X ω) ∂μ) ≠ Real.exp (t * k^4 / 8) := by
  have hp : 0 < t * k^4 / 8 := by positivity
  have he : 1 < Real.exp (t * k^4 / 8) := Real.one_lt_exp_iff.mpr hp
  have hb := cosine_expectation_le_one μ X hX k
  linarith

end OperatorDerivativeRewrite.Foundation.ManuscriptGeneratorDiagnostics
