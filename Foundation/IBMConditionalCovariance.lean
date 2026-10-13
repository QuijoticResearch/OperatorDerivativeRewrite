import Foundation.IBMConditionalMoments

/-! Exact two-time covariance of the composed scenery, conditional on a clock sample. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMConditionalCovariance
open InfiniteGaussian IBMSourceLaws IBMModificationBridge IBMContinuousComposition

/-- Covariance is invariant under a.e. replacement of both coordinates. -/
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

/-- For a fixed clock sample, the IBM scenery section has the two-sided
Brownian covariance kernel evaluated at absolute clock values. -/
theorem conditional_covariance
    (hmodS : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r)
    (s t : ℝ≥0) (ωY : SampleSpace) :
    cov[(fun ωX => value (sceneryPath S hS) (clockPath C hC) s (ωX,ωY)),
        (fun ωX => value (sceneryPath S hS) (clockPath C hC) t (ωX,ωY));
        gaussianProduct] =
      (|C s ωY| + |C t ωY| - abs (|C t ωY| - |C s ωY|)) / 2 := by
  have hs := hmodS |C s ωY|
  have ht := hmodS |C t ωY|
  have he := covariance_congr_ae gaussianProduct hs ht
  convert he.trans (sceneryBase_covariance |C s ωY| |C t ωY|) using 1 <;>
    simp only [value_eq, sceneryPath_apply, clockPath_apply, abs_abs]

end OperatorDerivativeRewrite.Foundation.IBMConditionalCovariance
