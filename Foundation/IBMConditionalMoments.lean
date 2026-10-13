import Foundation.IBMConditionalMixture
import Mathlib.Probability.Moments.Variance

/-! Exact conditional first and second moments of the genuine composed path,
under the explicit continuous-modification hypotheses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMConditionalMoments
open InfiniteGaussian IBMSourceLaws IBMModificationBridge IBMContinuousComposition IBMConditionalMixture

/-- The centered Gaussian with variance v has actual second moment v. -/
theorem gaussian_zero_second (v : ℝ≥0) :
    (∫ z : ℝ, z^2 ∂gaussianReal 0 v) = v := by
  have hv := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id.aemeasurable] at hv
  simpa only [integral_id_gaussianReal, id_eq, sub_zero] using hv

variable (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
  (hS : ∀ ω, Continuous (fun r => S r ω))
  (hC : ∀ ω, Continuous (fun t => C t ω))

/-- Conditional on each fixed clock sample, the scenery section is centered. -/
theorem conditional_mean
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r) (t : ℝ≥0) (ωY : SampleSpace) :
    (∫ ωX, value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY)
      ∂gaussianProduct) = 0 := by
  have hl := sceneryPath_gaussian_law S hS hmodS |C t ωY|
  have he := hl.integral_eq
  simpa only [value_eq, sceneryPath_apply, clockPath_apply,
    integral_id_gaussianReal] using he

/-- Conditional second moment is exactly the absolute Brownian clock value. -/
theorem conditional_second
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r) (t : ℝ≥0) (ωY : SampleSpace) :
    (∫ ωX, (value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY))^2
      ∂gaussianProduct) = |C t ωY| := by
  have hl := sceneryPath_gaussian_law S hS hmodS |C t ωY|
  have he := hl.integral_comp (f := fun z : ℝ => z^2) (by fun_prop)
  have hcast : ((⟨|C t ωY|, abs_nonneg _⟩ : ℝ≥0) : ℝ) = |C t ωY| := rfl
  calc
    (∫ ωX, (value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY))^2
        ∂gaussianProduct)
      = (∫ ωX, (sceneryPath S hS ωX |C t ωY|)^2 ∂gaussianProduct) := by
          rfl
    _ = (∫ z : ℝ, z^2 ∂gaussianReal 0 ⟨|C t ωY|, abs_nonneg _⟩) := by
          simpa only [Function.comp_def, abs_abs] using he
    _ = |C t ωY| := by
          rw [gaussian_zero_second]
          exact hcast
end OperatorDerivativeRewrite.Foundation.IBMConditionalMoments
