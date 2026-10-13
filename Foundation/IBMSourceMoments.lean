import Foundation.IBMSourceLaws
import Foundation.FractionalControlledEstimate

/-! Exact fourth moments of the verified Gaussian source increments, a
quantitative input for constructing continuous Brownian modifications. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSourceMoments
open InfiniteGaussian FractionalSpectralKernel FractionalSpectralGeometry
open FractionalControlledEstimate SeparableHilbertEmbedding GaussianHilbertProcess
attribute [local instance] spectralSpace_secondCountable
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

/-- Fourth moment of the actual infinite-dimensional first-chaos variable. -/
theorem firstChaos_fourth (h : CoefficientSpace) :
    (∫ ω, (firstChaosEmbedding h ω)^4 ∂gaussianProduct) = 3 * (‖h‖^2)^2 := by
  have he : (∫ ω, (firstChaosEmbedding h ω)^4 ∂gaussianProduct) =
      inner ℝ (square h) (square h) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [square_coeFn h] with ω hw
    rw [hw]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    ring
  rw [he, real_inner_self_eq_norm_sq, square_norm_sq]

/-- The true two-sided scenery has Brownian fourth-order increment scaling. -/
theorem sceneryBase_increment_fourth (s t : ℝ) :
    (∫ ω, (IBMSourceLaws.sceneryBase t ω - IBMSourceLaws.sceneryBase s ω)^4
      ∂gaussianProduct) = 3 * |t-s|^2 := by
  let v : SpectralSpace := normalized (1/2) (by norm_num) (by norm_num) t -
    normalized (1/2) (by norm_num) (by norm_num) s
  let h : CoefficientSpace := hilbertEmbedding SpectralSpace v
  have he : (fun ω => (IBMSourceLaws.sceneryBase t ω - IBMSourceLaws.sceneryBase s ω)^4) =ᵐ[gaussianProduct]
      (fun ω => (firstChaosEmbedding h ω)^4) := by
    filter_upwards [isonormal_sub_ae
      (normalized (1/2) (by norm_num) (by norm_num) t)
      (normalized (1/2) (by norm_num) (by norm_num) s)] with ω hw
    have hm : IBMSourceLaws.sceneryBase t ω - IBMSourceLaws.sceneryBase s ω =
        firstChaosEmbedding h ω := by
      convert hw.symm using 1 <;> rfl
    rw [hm]
  rw [integral_congr_ae he, firstChaos_fourth]
  have hn : ‖h‖^2 = |t-s| := by
    dsimp [h]
    rw [(hilbertEmbedding SpectralSpace).norm_map]
    simpa [v] using normalized_sub_norm_sq (1/2) (by norm_num) (by norm_num) s t
  rw [hn]

/-- Brownian clock increments have the matching fourth moment on their
actual source factor, for every ordered pair of nonnegative times. -/
theorem clockBase_increment_fourth (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, (GaussianTimeProcess.process t ω - GaussianTimeProcess.process s ω)^4
      ∂gaussianProduct) = 3 * ((t : ℝ)-s)^2 := by
  let v : GaussianTimeHilbert.TimeHilbert :=
    GaussianTimeHilbert.timeVector t - GaussianTimeHilbert.timeVector s
  let h : CoefficientSpace := hilbertEmbedding GaussianTimeHilbert.TimeHilbert v
  have he : (fun ω => (GaussianTimeProcess.process t ω -
      GaussianTimeProcess.process s ω)^4) =ᵐ[gaussianProduct]
      (fun ω => (firstChaosEmbedding h ω)^4) := by
    filter_upwards [isonormal_sub_ae
      (GaussianTimeHilbert.timeVector t) (GaussianTimeHilbert.timeVector s)] with ω hw
    have hm : GaussianTimeProcess.process t ω - GaussianTimeProcess.process s ω =
        firstChaosEmbedding h ω := by
      simpa [GaussianTimeProcess.process, GaussianTimeProcess.wienerL2,
        isonormal, h, v, GaussianHilbertProcess.isonormalEmbedding] using hw.symm
    rw [hm]
  rw [integral_congr_ae he, firstChaos_fourth]
  have hn : ‖h‖^2 = (t : ℝ)-s := by
    dsimp [h]
    rw [(hilbertEmbedding GaussianTimeHilbert.TimeHilbert).norm_map]
    simpa [v] using GaussianTimeHilbert.timeVector_sub_norm_sq s t hst
  rw [hn]
end OperatorDerivativeRewrite.Foundation.IBMSourceMoments
