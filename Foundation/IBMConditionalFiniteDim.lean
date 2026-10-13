import Foundation.IBMConditionalCovariance

/-! Coherent finite-dimensional conditional Gaussian laws for the IBM composition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMConditionalFiniteDim
open InfiniteGaussian IBMSourceLaws IBMModificationBridge IBMContinuousComposition

variable (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
  (hS : ∀ ω, Continuous (fun r => S r ω))
  (hC : ∀ ω, Continuous (fun t => C t ω))

/-- At every fixed clock sample, the entire scenery section indexed by
nonnegative time is a Gaussian process, hence all its finite-dimensional
distributions are jointly Gaussian with the covariance proved separately. -/
theorem conditional_isGaussianProcess
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (ωY : SampleSpace) :
    IsGaussianProcess
      (fun t ωX => value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY))
      gaussianProduct := by
  have hb := sceneryBase_isGaussianProcess.comp_right (fun t : ℝ≥0 => |C t ωY|)
  apply hb.congr
  intro t
  simpa only [Function.comp_def, value_eq, sceneryPath_apply, clockPath_apply] using
    (hmodS |C t ωY|).symm

/-- Every finite vector of IBM observations is conditionally Gaussian on the
scenery factor, for each fixed clock sample. -/
theorem conditional_finite_dim_gaussian
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (ωY : SampleSpace) (I : Finset ℝ≥0) :
    HasGaussianLaw
      (fun ωX => I.restrict (fun t =>
        value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY)))
      gaussianProduct :=
  (conditional_isGaussianProcess S C hS hC hmodS ωY).hasGaussianLaw I

end OperatorDerivativeRewrite.Foundation.IBMConditionalFiniteDim
