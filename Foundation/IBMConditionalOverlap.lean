import Foundation.IBMSpatialOverlap

/-! Conditional covariance of two IBM increments is signed spatial overlap. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace OperatorDerivativeRewrite.Foundation.IBMConditionalOverlap
open InfiniteGaussian IBMSourceLaws IBMModificationBridge IBMContinuousComposition IBMSpatialOverlap

private theorem covariance_congr_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hEX : μ[X] = μ[X'] := integral_congr_ae hX
  have hEY : μ[Y] = μ[Y'] := integral_congr_ae hY
  unfold covariance
  apply integral_congr_ae
  filter_upwards [hX, hY] with ω hx hy
  rw [hx, hy, hEX, hEY]

variable (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)
  (hS : ∀ ω, Continuous (fun r => S r ω))
  (hC : ∀ ω, Continuous (fun t => C t ω))

/-- Given a clock sample, any two IBM increments have conditional scenery
covariance equal to the signed overlap of their reflected-clock intervals. -/
theorem conditional_increment_covariance
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (s t u v : ℝ≥0) (ωY : SampleSpace) :
    cov[(fun ωX => value (sceneryPath S hS) (clockPath C hC) t (ωX, ωY) -
      value (sceneryPath S hS) (clockPath C hC) s (ωX, ωY)),
      (fun ωX => value (sceneryPath S hS) (clockPath C hC) v (ωX, ωY) -
      value (sceneryPath S hS) (clockPath C hC) u (ωX, ωY)); gaussianProduct] =
      signedOverlap |C s ωY| |C t ωY| |C u ωY| |C v ωY| := by
  have hst : (fun ωX => value (sceneryPath S hS) (clockPath C hC) t (ωX, ωY) -
      value (sceneryPath S hS) (clockPath C hC) s (ωX, ωY)) =ᵐ[gaussianProduct]
      (fun ωX => sceneryBase |C t ωY| ωX - sceneryBase |C s ωY| ωX) := by
    filter_upwards [hmodS |C t ωY|, hmodS |C s ωY|] with ωX ht hs
    simp only [value_eq, sceneryPath_apply, clockPath_apply, ht, hs]
  have huv : (fun ωX => value (sceneryPath S hS) (clockPath C hC) v (ωX, ωY) -
      value (sceneryPath S hS) (clockPath C hC) u (ωX, ωY)) =ᵐ[gaussianProduct]
      (fun ωX => sceneryBase |C v ωY| ωX - sceneryBase |C u ωY| ωX) := by
    filter_upwards [hmodS |C v ωY|, hmodS |C u ωY|] with ωX hv hu
    simp only [value_eq, sceneryPath_apply, clockPath_apply, hv, hu]
  rw [covariance_congr_ae gaussianProduct hst huv]
  exact sceneryBase_increment_covariance _ _ _ _ (abs_nonneg _) (abs_nonneg _)
    (abs_nonneg _) (abs_nonneg _)

end OperatorDerivativeRewrite.Foundation.IBMConditionalOverlap
