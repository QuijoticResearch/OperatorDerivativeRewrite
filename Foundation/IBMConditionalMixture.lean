import Foundation.IBMModificationBridge
import Mathlib.MeasureTheory.Measure.Prod

/-! Genuine Gaussian-mixture event law for a continuous IBM composition,
conditional on explicit a.e. continuous modifications of the verified sources. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMConditionalMixture
open InfiniteGaussian IBMSourceLaws IBMModificationBridge IBMContinuousComposition
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

/-- The incoming spectral scenery has the exact centered Gaussian law on its
original factor, independently of the clock product construction. -/
theorem sceneryBase_gaussian_law (r : ℝ) :
    HasLaw (sceneryBase r) (gaussianReal 0 ⟨|r|, abs_nonneg r⟩) gaussianProduct := by
  refine ⟨(sceneryBase_measurable r).aemeasurable, ?_⟩
  unfold sceneryBase
  rw [GaussianHilbertProcess.isonormal_law]
  apply congrArg (gaussianReal 0)
  apply NNReal.eq
  simp only [NNReal.coe_mk]
  norm_num [FractionalSpectralGeometry.normalized_norm_sq] <;> rfl

variable (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
  (hS : ∀ ω, Continuous (fun r => S r ω))
  (hC : ∀ ω, Continuous (fun t => C t ω))

/-- Every deterministic-time coordinate of the continuous scenery modification
retains the exact Gaussian law. -/
theorem sceneryPath_gaussian_law
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r) (r : ℝ) :
    HasLaw (fun ω => sceneryPath S hS ω r)
      (gaussianReal 0 ⟨|r|, abs_nonneg r⟩) gaussianProduct :=
  (sceneryBase_gaussian_law r).congr (hmodS r)

/-- For every fixed clock sample, the scenery section is Gaussian with
variance equal to the absolute clock value. -/
theorem conditional_event
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r) (t : ℝ≥0) (ωY : SampleSpace)
    (A : Set ℝ) (hA : MeasurableSet A) :
    gaussianProduct {ωX | value (sceneryPath S hS) (clockPath C hC) t (ωX, ωY) ∈ A} =
      gaussianReal 0 ⟨|C t ωY|, abs_nonneg _⟩ A := by
  have hl := sceneryPath_gaussian_law S hS hmodS |C t ωY|
  simpa [value_eq, clockPath_apply, sceneryPath_apply] using
    (hl.measure_eq (p := fun z => z ∈ A) hA)

/-- The actual composed process has the clock mixture of Gaussian event laws.
This is a distribution statement about one process on the joint probability space. -/
theorem mixture_event
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (hmS : ∀ r, Measurable (S r))
    (hmC : ∀ t, Measurable (C t)) (t : ℝ≥0)
    (A : Set ℝ) (hA : MeasurableSet A) :
    jointMeasure {ω | value (sceneryPath S hS) (clockPath C hC) t ω ∈ A} =
      ∫⁻ ωY, gaussianReal 0 ⟨|C t ωY|, abs_nonneg _⟩ A ∂gaussianProduct := by
  have hX := sceneryPath_measurable S hS hmS
  have hY := clockPath_measurable C hC hmC
  have hE : MeasurableSet
      {ω : JointSample | value (sceneryPath S hS) (clockPath C hC) t ω ∈ A} :=
    hA.preimage (value_measurable _ _ hX hY t)
  rw [jointMeasure, Measure.prod_apply_symm hE]
  congr 1
  funext ωY
  exact conditional_event S C hS hC hmodS t ωY A hA

end OperatorDerivativeRewrite.Foundation.IBMConditionalMixture
