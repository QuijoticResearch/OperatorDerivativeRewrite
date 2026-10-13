import Foundation.IBMConditionalReflectedMoments

/-! Exact finite-family conditional quartic expectation for IBM increments. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace OperatorDerivativeRewrite.Foundation.IBMFiniteQuartic
open InfiniteGaussian IBMSourceLaws IBMModificationBridge IBMContinuousComposition
open IBMConditionalIncrements IBMReflectedClockCorrection IBMConditionalReflectedMoments
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

variable (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
  (hS : ∀ ω, Continuous (fun r => S r ω))
  (hC : ∀ ω, Continuous (fun t => C t ω))

private theorem sceneryBase_memLp_four (r : ℝ) :
    MemLp (sceneryBase r) 4 gaussianProduct := by
  unfold sceneryBase
  exact GaussianHilbertProcess.isonormal_memLp _ 4 (by simp)

/-- Each conditional IBM increment has an integrable fourth power. -/
theorem conditional_increment_fourth_integrable
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (s t : ℝ≥0) (ωY : SampleSpace) :
    Integrable (fun ωX => (value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY) -
      value (sceneryPath S hS) (clockPath C hC) s (ωX,ωY))^4)
      gaussianProduct := by
  have ht : MemLp (S |C t ωY|) 4 gaussianProduct :=
    (memLp_congr_ae (hmodS |C t ωY|)).2 (sceneryBase_memLp_four |C t ωY|)
  have hs : MemLp (S |C s ωY|) 4 gaussianProduct :=
    (memLp_congr_ae (hmodS |C s ωY|)).2 (sceneryBase_memLp_four |C s ωY|)
  have hdiff : MemLp (fun ωX => S |C t ωY| ωX - S |C s ωY| ωX) 4 gaussianProduct :=
    ht.sub hs
  have hi := hdiff.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  convert hi using 1
  ext ωX
  simp only [value_eq, sceneryPath_apply, clockPath_apply]
  simp [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity :
    0 ≤ (S |C t ωY| ωX - S |C s ωY| ωX)^4)]

/-- Fourth-power sum over a finite family of physical-time intervals. -/
def quarticSum (I : Finset (ℝ≥0 × ℝ≥0)) (ωX : SampleSpace) (ωY : SampleSpace) : ℝ :=
  ∑ p ∈ I, (value (sceneryPath S hS) (clockPath C hC) p.2 (ωX,ωY) -
    value (sceneryPath S hS) (clockPath C hC) p.1 (ωX,ωY))^4

/-- The conditional expectation of any finite quartic sum is exactly
three times the sum of squared reflected-clock displacements. -/
theorem conditional_quarticSum_expectation
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (I : Finset (ℝ≥0 × ℝ≥0)) (ωY : SampleSpace) :
    (∫ ωX, quarticSum S C hS hC I ωX ωY ∂gaussianProduct) =
      ∑ p ∈ I, 3 * (|C p.2 ωY| - |C p.1 ωY|)^2 := by
  classical
  unfold quarticSum
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro p hp
    simpa only [sq_abs] using
      conditional_increment_fourth S C hS hC hmodS p.1 p.2 ωY
  · intro p hp
    exact conditional_increment_fourth_integrable S C hS hC hmodS p.1 p.2 ωY


/-- The exact finite-family correction is the sum of individual
zero-crossing penalties; no independence assumption is involved. -/
theorem conditional_quarticSum_crossing
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (I : Finset (ℝ≥0 × ℝ≥0)) (ωY : SampleSpace) :
    (∫ ωX, quarticSum S C hS hC I ωX ωY ∂gaussianProduct) =
      ∑ p ∈ I, 3 * ((C p.2 ωY - C p.1 ωY)^2 -
        crossingPenalty (C p.1 ωY) (C p.2 ωY)) := by
  rw [conditional_quarticSum_expectation S C hS hC hmodS]
  apply Finset.sum_congr rfl
  intro p hp
  rw [reflected_increment_sq]

/-- The unreflected-clock quadratic sum bounds the finite conditional
quartic expectation. -/
theorem conditional_quarticSum_le
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (I : Finset (ℝ≥0 × ℝ≥0)) (ωY : SampleSpace) :
    (∫ ωX, quarticSum S C hS hC I ωX ωY ∂gaussianProduct) ≤
      ∑ p ∈ I, 3 * (C p.2 ωY - C p.1 ωY)^2 := by
  rw [conditional_quarticSum_crossing S C hS hC hmodS]
  apply Finset.sum_le_sum
  intro p hp
  have h := (crossingPenalty_bounds (C p.1 ωY) (C p.2 ωY)).1
  linarith
end OperatorDerivativeRewrite.Foundation.IBMFiniteQuartic
