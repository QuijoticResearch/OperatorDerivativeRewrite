import Foundation.IBMConditionalObservable
import Foundation.IBMFiniteQuartic

/-! Finite IBM quartic variation is measurable in the observable path sigma-algebra. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace OperatorDerivativeRewrite.Foundation.IBMObservableQuartic
open InfiniteGaussian IBMSourceLaws IBMContinuousComposition IBMConditionalObservable

variable (X : SampleSpace → C(ℝ, ℝ)) (Y : SampleSpace → C(ℝ≥0, ℝ))

/-- Each IBM composition coordinate is measurable for the sigma-algebra
it generates, without requiring ambient source-path measurability. -/
theorem observable_value_measurable (t : ℝ≥0) :
    Measurable[observableSigma X Y] (value X Y t) := by
  change Measurable[MeasurableSpace.comap
      (fun w : JointSample => fun r : ℝ≥0 => value X Y r w) inferInstance]
      (fun w => (fun r : ℝ≥0 => value X Y r w) t)
  exact (measurable_pi_apply t).comp
    (comap_measurable (fun w : JointSample => fun r : ℝ≥0 => value X Y r w))

/-- Finite fourth-power variation depends only on the observed IBM path. -/
def finiteQuartic (I : Finset (ℝ≥0 × ℝ≥0)) (ω : JointSample) : ℝ :=
  ∑ p ∈ I, (value X Y p.2 ω - value X Y p.1 ω)^4

/-- Finite quartic variation is measurable in the intrinsic observable
sigma-algebra of the supplied composition. -/
theorem finiteQuartic_observable_measurable
    (I : Finset (ℝ≥0 × ℝ≥0)) :
    Measurable[observableSigma X Y] (finiteQuartic X Y I) := by
  classical
  letI : MeasurableSpace JointSample := observableSigma X Y
  change Measurable (finiteQuartic X Y I)
  unfold finiteQuartic
  apply Finset.measurable_sum
  intro p hp
  exact ((observable_value_measurable X Y p.2).sub
    (observable_value_measurable X Y p.1)).pow_const 4


/-- The observable path functional is exactly the finite quartic sum used
in the verified conditional moment and variance formulas. -/
theorem finiteQuartic_eq_conditional_sum
    (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hC : ∀ ω, Continuous (fun t => C t ω))
    (I : Finset (ℝ≥0 × ℝ≥0)) (ω : JointSample) :
    finiteQuartic (IBMModificationBridge.sceneryPath S hS)
      (IBMModificationBridge.clockPath C hC) I ω =
      IBMFiniteQuartic.quarticSum S C hS hC I ω.1 ω.2 := rfl
end OperatorDerivativeRewrite.Foundation.IBMObservableQuartic
