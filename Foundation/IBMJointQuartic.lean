import Foundation.IBMClockQuarticBound
import Foundation.IBMObservableQuartic
import Mathlib.MeasureTheory.Integral.Prod

/-! Joint product-law integrability and expectation for finite IBM quartic sums. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace OperatorDerivativeRewrite.Foundation.IBMJointQuartic
open InfiniteGaussian IBMSourceLaws IBMModificationBridge IBMContinuousComposition
open IBMFiniteQuartic IBMClockQuarticBound

variable (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
  (hS : ∀ ω, Continuous (fun r => S r ω))
  (hC : ∀ ω, Continuous (fun t => C t ω))
  (hmS : ∀ r, Measurable (S r)) (hmC : ∀ t, Measurable (C t))
  (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
  (hmodC : ∀ r, C r =ᵐ[gaussianProduct] GaussianTimeProcess.process r)

/-- A finite quartic sum is measurable under the joint source measure. -/
theorem quarticSum_measurable
    (hmS : ∀ r, Measurable (S r)) (hmC : ∀ t, Measurable (C t))
    (I : Finset (ℝ≥0 × ℝ≥0)) :
    Measurable (fun ω : JointSample => quarticSum S C hS hC I ω.1 ω.2) := by
  classical
  unfold quarticSum
  apply Finset.measurable_sum
  intro p hp
  exact ((value_measurable _ _ (sceneryPath_measurable S hS hmS)
    (clockPath_measurable C hC hmC) p.2).sub
    (value_measurable _ _ (sceneryPath_measurable S hS hmS)
    (clockPath_measurable C hC hmC) p.1)).pow_const 4

private theorem quarticSum_nonneg (I : Finset (ℝ≥0 × ℝ≥0))
    (ω : JointSample) : 0 ≤ quarticSum S C hS hC I ω.1 ω.2 := by
  unfold quarticSum
  exact Finset.sum_nonneg (fun p hp => by positivity)

/-- The actual finite IBM quartic observable is integrable on the joint
product law, provided measurable continuous modifications are supplied. -/
theorem quarticSum_integrable
    (hmS : ∀ r, Measurable (S r)) (hmC : ∀ t, Measurable (C t))
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (hmodC : ∀ r, C r =ᵐ[gaussianProduct] GaussianTimeProcess.process r)
    (I : Finset (ℝ≥0 × ℝ≥0)) :
    Integrable (fun ω : JointSample => quarticSum S C hS hC I ω.1 ω.2)
      jointMeasure := by
  let f : JointSample → ℝ := fun ω => quarticSum S C hS hC I ω.1 ω.2
  have hmeas : Measurable f := quarticSum_measurable S C hS hC hmS hmC I
  apply (integrable_prod_iff' hmeas.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (fun ωY => by
      unfold f quarticSum
      apply integrable_finsetSum
      intro p hp
      exact conditional_increment_fourth_integrable S C hS hC hmodS p.1 p.2 ωY)
  · have heq (ωY : SampleSpace) :
        (∫ ωX, ‖f (ωX, ωY)‖ ∂gaussianProduct) =
          ∑ p ∈ I, 3 * (|C p.2 ωY| - |C p.1 ωY|)^2 := by
      have hn (ωX : SampleSpace) : ‖f (ωX, ωY)‖ = f (ωX, ωY) := by
        exact Real.norm_eq_abs _ |>.trans (abs_of_nonneg (quarticSum_nonneg S C hS hC I (ωX,ωY)))
      simp_rw [hn]
      exact conditional_quarticSum_expectation S C hS hC hmodS I ωY
    simp_rw [heq]
    apply integrable_finsetSum
    intro p hp
    exact (clock_reflected_increment_integrable C hmodC p.1 p.2).const_mul 3

/-- Fubini identifies the finite joint expectation with the clock average
of the exact conditional scenery expectation. -/
theorem joint_quarticSum_expectation
    (hmS : ∀ r, Measurable (S r)) (hmC : ∀ t, Measurable (C t))
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (hmodC : ∀ r, C r =ᵐ[gaussianProduct] GaussianTimeProcess.process r)
    (I : Finset (ℝ≥0 × ℝ≥0)) :
    (∫ ω, quarticSum S C hS hC I ω.1 ω.2 ∂jointMeasure) =
      ∫ ωY, ∑ p ∈ I, 3 * (|C p.2 ωY| - |C p.1 ωY|)^2
        ∂gaussianProduct := by
  unfold jointMeasure
  rw [integral_prod_symm _ (quarticSum_integrable S C hS hC hmS hmC hmodS hmodC I)]
  simp_rw [conditional_quarticSum_expectation S C hS hC hmodS I]

/-- A finite ordered interval family has joint quartic expectation at most
three times its total physical length. -/
theorem joint_quarticSum_le
    (hmS : ∀ r, Measurable (S r)) (hmC : ∀ t, Measurable (C t))
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (hmodC : ∀ r, C r =ᵐ[gaussianProduct] GaussianTimeProcess.process r)
    (I : Finset (ℝ≥0 × ℝ≥0))
    (hI : ∀ p ∈ I, p.1 ≤ p.2) :
    (∫ ω, quarticSum S C hS hC I ω.1 ω.2 ∂jointMeasure) ≤
      3 * ∑ p ∈ I, ((p.2 : ℝ) - p.1) := by
  unfold jointMeasure
  rw [integral_prod_symm _ (quarticSum_integrable S C hS hC hmS hmC hmodS hmodC I)]
  exact averaged_conditional_quarticSum_le S C hS hC hmodS hmodC I hI

end OperatorDerivativeRewrite.Foundation.IBMJointQuartic
