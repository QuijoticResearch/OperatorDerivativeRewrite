import Foundation.GaussianTimeSpaceHermite

/-! Eighth mixed moments of two correlated Gaussian first-chaos variables. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace OperatorDerivativeRewrite.Foundation.GaussianQuarticWick
open InfiniteGaussian GaussianTimeSpaceHermite

/-- The fourth Hermite polynomial is `x⁴ - 6tx² + 3t²`. -/
theorem value_four (x t : ℝ) :
    value 4 x t = x^4 - 6 * t * x^2 + 3 * t^2 := by
  have h3 : value 3 x t = x * (x^2 - t) - 2 * t * x := by
    convert value_recursion 1 x t using 1; norm_num [value_two, value_one]
  have h4 : value 4 x t = x * value 3 x t - 3 * t * value 2 x t := by
    convert value_recursion 2 x t using 1; norm_num
  rw [h4, h3, value_two]
  ring

/-- Fourth powers decomposed into fourth, second, and zeroth Wiener chaoses. -/
def quartic (h : CoefficientSpace) : GaussianL2 :=
  (wick h 4 : GaussianL2) + (6 * ‖h‖^2 : ℝ) • (wick h 2 : GaussianL2) +
    (3 * (‖h‖^2)^2 : ℝ) • (wick h 0 : GaussianL2)

/-- The Wick decomposition represents the actual fourth power a.e. -/
theorem quartic_coeFn (h : CoefficientSpace) :
    quartic h =ᵐ[gaussianProduct] fun ω => (firstChaosEmbedding h ω)^4 := by
  filter_upwards [Lp.coeFn_add
      ((wick h 4 : GaussianL2) + (6 * ‖h‖^2 : ℝ) • (wick h 2 : GaussianL2))
      ((3 * (‖h‖^2)^2 : ℝ) • (wick h 0 : GaussianL2)),
    Lp.coeFn_add (wick h 4 : GaussianL2)
      ((6 * ‖h‖^2 : ℝ) • (wick h 2 : GaussianL2)),
    Lp.coeFn_smul (6 * ‖h‖^2 : ℝ) (wick h 2 : GaussianL2),
    Lp.coeFn_smul (3 * (‖h‖^2)^2 : ℝ) (wick h 0 : GaussianL2),
    core_coeFn h (‖h‖^2) 4,
    core_coeFn h (‖h‖^2) 2,
    core_coeFn h (‖h‖^2) 0] with ω ha hb hc hd h4 h2 h0
  rw [quartic, ha]
  simp only [Pi.add_apply]
  rw [hb]
  simp only [Pi.add_apply]
  rw [hc, hd]
  simp only [wick, Pi.smul_apply]
  rw [h4, h2, h0]
  simp only [smul_eq_mul, value_four,
    value_two, value_zero]
  ring

/-- Isserlis' eighth-order identity, proved from actual Gaussian Wick
orthogonality, including degenerate and fully correlated cases. -/
theorem quartic_inner (h k : CoefficientSpace) :
    inner ℝ (quartic h) (quartic k) =
      9 * (‖h‖^2)^2 * (‖k‖^2)^2 +
      72 * (‖h‖^2) * (‖k‖^2) * (inner ℝ h k)^2 +
      24 * (inner ℝ h k)^4 := by
  simp only [quartic, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, wick_inner]
  norm_num
  ring

/-- Mixed fourth-power expectation for the actual measurable Gaussian
representatives on the source product probability space. -/
theorem firstChaos_fourth_product (h k : CoefficientSpace) :
    (∫ ω, (firstChaosEmbedding h ω)^4 * (firstChaosEmbedding k ω)^4
      ∂gaussianProduct) =
      9 * (‖h‖^2)^2 * (‖k‖^2)^2 +
      72 * (‖h‖^2) * (‖k‖^2) * (inner ℝ h k)^2 +
      24 * (inner ℝ h k)^4 := by
  have he : (∫ ω, (firstChaosEmbedding h ω)^4 * (firstChaosEmbedding k ω)^4
      ∂gaussianProduct) = inner ℝ (quartic h) (quartic k) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [quartic_coeFn h, quartic_coeFn k] with ω hh hk
    rw [hh, hk]
    norm_num
    ring
  rw [he, quartic_inner]

end OperatorDerivativeRewrite.Foundation.GaussianQuarticWick
