import Foundation.IBMFiniteQuartic
import Foundation.IBMConditionalQuarticPair

/-! Integrability and double-sum expansion for finite IBM quartic families. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace OperatorDerivativeRewrite.Foundation.IBMFiniteQuarticSecondMoment
open InfiniteGaussian IBMSourceLaws IBMModificationBridge IBMContinuousComposition
open IBMConditionalQuarticPair IBMFiniteQuartic
open GaussianQuarticWick GaussianHilbertProcess SeparableHilbertEmbedding
open FractionalSpectralKernel FractionalSpectralGeometry
attribute [local instance] spectralSpace_secondCountable

variable (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
  (hS : ∀ ω, Continuous (fun r => S r ω))
  (hC : ∀ ω, Continuous (fun t => C t ω))

/-- Each fixed-clock fourth-power increment is genuinely in scenery L².
This justifies products and finite second-moment expansions. -/
theorem conditional_fourth_memLp_two
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (s t : ℝ≥0) (ωY : SampleSpace) :
    MemLp (fourthPower S C hS hC s t ωY) 2 gaussianProduct := by
  let h : CoefficientSpace :=
    hilbertEmbedding SpectralSpace
      (normalized (1/2) (by norm_num) (by norm_num) |C t ωY| -
        normalized (1/2) (by norm_num) (by norm_num) |C s ωY|)
  have hae : (fourthPower S C hS hC s t ωY) =ᵐ[gaussianProduct]
      (quartic h : GaussianL2) := by
    filter_upwards [hmodS |C t ωY|, hmodS |C s ωY|,
      isonormal_sub_ae
        (normalized (1/2) (by norm_num) (by norm_num) |C t ωY|)
        (normalized (1/2) (by norm_num) (by norm_num) |C s ωY|),
      (quartic_coeFn h).symm] with ωX ht hs hsub hq
    change (value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY) -
      value (sceneryPath S hS) (clockPath C hC) s (ωX,ωY))^4 =
        (quartic h : GaussianL2) ωX
    simp only [value_eq, sceneryPath_apply, clockPath_apply, ht, hs]
    have he : sceneryBase |C t ωY| ωX - sceneryBase |C s ωY| ωX =
        firstChaosEmbedding h ωX := by
      convert hsub.symm using 1 <;> rfl
    rw [he]
    exact hq
  exact (memLp_congr_ae hae).2 (Lp.memLp (quartic h))

/-- Products of two fourth-power increments are integrable on the
scenery factor at every fixed clock sample. -/
theorem conditional_fourth_product_integrable
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (s t u v : ℝ≥0) (ωY : SampleSpace) :
    Integrable (fun ωX => fourthPower S C hS hC s t ωY ωX *
      fourthPower S C hS hC u v ωY ωX) gaussianProduct := by
  have h1 := conditional_fourth_memLp_two S C hS hC hmodS s t ωY
  have h2 := conditional_fourth_memLp_two S C hS hC hmodS u v ωY
  exact (h1.fun_mul h2 : MemLp _ 1 gaussianProduct).integrable (by simp)


/-- The conditional scenery second moment of a finite quartic sum expands
as the exact double sum of its pair-increment product moments. -/
theorem conditional_quarticSum_second_moment_expand
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (I : Finset (ℝ≥0 × ℝ≥0)) (ωY : SampleSpace) :
    (∫ ωX, (quarticSum S C hS hC I ωX ωY)^2 ∂gaussianProduct) =
      ∑ p ∈ I, ∑ q ∈ I,
        ∫ ωX, fourthPower S C hS hC p.1 p.2 ωY ωX *
          fourthPower S C hS hC q.1 q.2 ωY ωX ∂gaussianProduct := by
  classical
  have hpoint (ωX : SampleSpace) :
      (quarticSum S C hS hC I ωX ωY)^2 =
        ∑ p ∈ I, ∑ q ∈ I,
          fourthPower S C hS hC p.1 p.2 ωY ωX *
            fourthPower S C hS hC q.1 q.2 ωY ωX := by
    change (∑ p ∈ I, fourthPower S C hS hC p.1 p.2 ωY ωX)^2 = _
    rw [pow_two, Finset.sum_mul_sum]
  calc
    (∫ ωX, (quarticSum S C hS hC I ωX ωY)^2 ∂gaussianProduct) =
      ∫ ωX, ∑ p ∈ I, ∑ q ∈ I,
        fourthPower S C hS hC p.1 p.2 ωY ωX *
          fourthPower S C hS hC q.1 q.2 ωY ωX ∂gaussianProduct := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
    _ = _ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [integral_finsetSum]
        intro q hq
        exact conditional_fourth_product_integrable S C hS hC hmodS
          p.1 p.2 q.1 q.2 ωY
      · intro p hp
        exact integrable_finsetSum I (fun q hq =>
          conditional_fourth_product_integrable S C hS hC hmodS
            p.1 p.2 q.1 q.2 ωY)

/-- The exact scenery-conditional variance of a finite IBM quartic sum is
a nonnegative double sum of spatial-overlap contributions. This formula
isolates the quantity that must be controlled in a partition limit. -/
theorem conditional_quarticSum_centered_second_moment
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (I : Finset (ℝ≥0 × ℝ≥0)) (ωY : SampleSpace) :
    (∫ ωX, (quarticSum S C hS hC I ωX ωY)^2 ∂gaussianProduct) -
      (∫ ωX, quarticSum S C hS hC I ωX ωY ∂gaussianProduct)^2 =
      ∑ p ∈ I, ∑ q ∈ I,
        (72 * abs (|C p.2 ωY| - |C p.1 ωY|) *
          abs (|C q.2 ωY| - |C q.1 ωY|) *
          (IBMSpatialOverlap.signedOverlap |C p.1 ωY| |C p.2 ωY|
            |C q.1 ωY| |C q.2 ωY|)^2 +
        24 * (IBMSpatialOverlap.signedOverlap |C p.1 ωY| |C p.2 ωY|
          |C q.1 ωY| |C q.2 ωY|)^4) := by
  classical
  have hmean :
      (∫ ωX, quarticSum S C hS hC I ωX ωY ∂gaussianProduct) =
        ∑ p ∈ I, ∫ ωX, fourthPower S C hS hC p.1 p.2 ωY ωX
          ∂gaussianProduct := by
    unfold quarticSum
    rw [integral_finsetSum I (by
      intro p hp
      exact IBMFiniteQuartic.conditional_increment_fourth_integrable S C hS hC
        hmodS p.1 p.2 ωY)]
    rfl
  rw [conditional_quarticSum_second_moment_expand S C hS hC hmodS, hmean,
    pow_two, Finset.sum_mul_sum]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  exact IBMConditionalQuarticPair.conditional_fourth_centered_product
    S C hS hC hmodS p.1 p.2 q.1 q.2 ωY
end OperatorDerivativeRewrite.Foundation.IBMFiniteQuarticSecondMoment
