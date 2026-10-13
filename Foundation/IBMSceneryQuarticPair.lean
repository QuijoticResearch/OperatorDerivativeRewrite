import Foundation.GaussianQuarticWick
import Foundation.IBMSpatialOverlap

/-! Mixed fourth powers of two actual Brownian-scenery increments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace OperatorDerivativeRewrite.Foundation.IBMSceneryQuarticPair
open InfiniteGaussian GaussianHilbertProcess SeparableHilbertEmbedding
open FractionalSpectralKernel FractionalSpectralGeometry IBMSourceLaws
open IBMSpatialOverlap GaussianQuarticWick
attribute [local instance] spectralSpace_secondCountable

private def direction (a b : ℝ) : CoefficientSpace :=
  hilbertEmbedding SpectralSpace
    (normalized (1/2) (by norm_num) (by norm_num) b -
      normalized (1/2) (by norm_num) (by norm_num) a)

private theorem direction_norm_sq (a b : ℝ) :
    ‖direction a b‖^2 = |b-a| := by
  unfold direction
  rw [(hilbertEmbedding SpectralSpace).norm_map]
  simpa using normalized_sub_norm_sq (1/2) (by norm_num) (by norm_num) a b

private theorem normalized_inner_min (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    inner ℝ (normalized (1/2) (by norm_num) (by norm_num) a)
      (normalized (1/2) (by norm_num) (by norm_num) b) = min a b := by
  have h := sceneryBase_covariance_min a b ha hb
  rw [show cov[sceneryBase a, sceneryBase b; gaussianProduct] =
    inner ℝ (normalized (1/2) (by norm_num) (by norm_num) a)
      (normalized (1/2) (by norm_num) (by norm_num) b) from
        isonormal_covariance _ _] at h
  exact h

private theorem direction_inner (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    inner ℝ (direction a b) (direction c d) = signedOverlap a b c d := by
  unfold direction
  rw [(hilbertEmbedding SpectralSpace).inner_map_map]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  rw [normalized_inner_min b d hb hd,
    normalized_inner_min b c hb hc,
    normalized_inner_min a d ha hd,
    normalized_inner_min a c ha hc]
  rw [signedOverlap_eq_min_covariance]
  ring

private theorem increment_ae (a b : ℝ) :
    (fun ω => sceneryBase b ω - sceneryBase a ω) =ᵐ[gaussianProduct]
      (fun ω => firstChaosEmbedding (direction a b) ω) := by
  filter_upwards [isonormal_sub_ae
    (normalized (1/2) (by norm_num) (by norm_num) b)
    (normalized (1/2) (by norm_num) (by norm_num) a)] with ω hw
  convert hw.symm using 1 <;> rfl

/-- Exact eighth mixed moment for two oriented nonnegative Brownian-scenery
intervals, expressed in terms of signed spatial overlap. -/
theorem scenery_increment_fourth_product
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (∫ ω, (sceneryBase b ω - sceneryBase a ω)^4 *
      (sceneryBase d ω - sceneryBase c ω)^4 ∂gaussianProduct) =
      9 * |b-a|^2 * |d-c|^2 +
      72 * |b-a| * |d-c| * (signedOverlap a b c d)^2 +
      24 * (signedOverlap a b c d)^4 := by
  have he : (fun ω => (sceneryBase b ω - sceneryBase a ω)^4 *
      (sceneryBase d ω - sceneryBase c ω)^4) =ᵐ[gaussianProduct]
      (fun ω => (firstChaosEmbedding (direction a b) ω)^4 *
        (firstChaosEmbedding (direction c d) ω)^4) := by
    filter_upwards [increment_ae a b, increment_ae c d] with ω h1 h2
    rw [h1, h2]
  rw [integral_congr_ae he, firstChaos_fourth_product,
    direction_norm_sq, direction_norm_sq, direction_inner a b c d ha hb hc hd]

end OperatorDerivativeRewrite.Foundation.IBMSceneryQuarticPair
