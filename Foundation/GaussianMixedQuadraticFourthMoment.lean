import Foundation.GaussianTwoSourceQuadraticMoments

/-! Exact centered two-source quadratic fourth moments and the sharp rank-two
bound. General completed quadratic fields remain a separate obligation. -/
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianMixedQuadraticFourthMoment
open InfiniteGaussian GaussianTimeSpaceHermite GaussianQuadraticSourceHodge
open GaussianTwoSourceQuadraticMoments GaussianQuarticWick IBMGaussianSteinMoments

def rawProductSquare (u v : CoefficientSpace) : polynomialCylindricalDomain :=
  polynomialProduct (rawProduct u v) (rawProduct u v)

theorem rawProductSquare_coeFn (u v : CoefficientSpace) :
    (rawProductSquare u v : GaussianL2) =ᵐ[gaussianProduct]
      fun ω => (firstChaosEmbedding u ω * firstChaosEmbedding v ω)^2 := by
  filter_upwards [polynomialProductL2_coeFn (rawProduct u v) (rawProduct u v),
    rawProduct_coeFn u v] with ω hs hp
  change polynomialProductL2 (rawProduct u v) (rawProduct u v) ω = _
  rw [hs, hp]
  ring

theorem cube_inner (u v : CoefficientSpace) :
    inner ℝ (cube u) (cube v) =
      9 * ‖u‖^2 * ‖v‖^2 * inner ℝ u v + 6 * (inner ℝ u v)^3 := by
  simp only [cube, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, wick_inner]
  norm_num
  ring

theorem rawProductSquare_raw_inner (u v : CoefficientSpace) :
    inner ℝ (rawProductSquare u v : GaussianL2) (rawProduct u v : GaussianL2) =
      9 * ‖u‖^2 * ‖v‖^2 * inner ℝ u v + 6 * (inner ℝ u v)^3 := by
  have he : inner ℝ (rawProductSquare u v : GaussianL2) (rawProduct u v : GaussianL2) =
      inner ℝ (cube u) (cube v) := by
    rw [L2_inner_eq_integral, L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [rawProductSquare_coeFn u v, rawProduct_coeFn u v,
      cube_coeFn u, cube_coeFn v] with ω hs hp hu hv
    rw [hs, hp, hu, hv]
    simp only [Real.inner_apply]
    ring
  rw [he, cube_inner]

theorem rawProductSquare_one_inner (u v : CoefficientSpace) :
    inner ℝ (rawProductSquare u v : GaussianL2) gaussianOne =
      ‖u‖^2 * ‖v‖^2 + 2 * (inner ℝ u v)^2 := by
  have he : inner ℝ (rawProductSquare u v : GaussianL2) gaussianOne =
      ‖(rawProduct u v : GaussianL2)‖^2 := by
    rw [L2_inner_eq_integral, BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [rawProductSquare_coeFn u v, rawProduct_coeFn u v,
      gaussianOne_coeFn] with ω hs hp h1
    rw [hs, hp, h1]
    simp only [Real.norm_eq_abs, sq_abs, Real.inner_apply, mul_one]
  rw [he, rawProduct_variance]

theorem rawProduct_one_inner (u v : CoefficientSpace) :
    inner ℝ (rawProduct u v : GaussianL2) gaussianOne = inner ℝ u v := by
  have he : inner ℝ (rawProduct u v : GaussianL2) gaussianOne =
      inner ℝ (firstChaosEmbedding u) (firstChaosEmbedding v) := by
    rw [L2_inner_eq_integral, L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [rawProduct_coeFn u v, gaussianOne_coeFn] with ω hp h1
    rw [hp, h1]
    simp only [Real.inner_apply, mul_one]
  rw [he, firstChaosEmbedding.inner_map_map]

def centeredProductSquare (u v : CoefficientSpace) : GaussianL2 :=
  (rawProductSquare u v : GaussianL2) - (2 * inner ℝ u v) • (rawProduct u v : GaussianL2) +
    (inner ℝ u v)^2 • gaussianOne

theorem centeredProductSquare_eq (u v : CoefficientSpace) :
    centeredProductSquare u v = (polynomialProduct (mixedPolynomial u v) (mixedPolynomial u v) : GaussianL2) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      ((rawProductSquare u v : GaussianL2) - (2 * inner ℝ u v) • (rawProduct u v : GaussianL2))
      ((inner ℝ u v)^2 • gaussianOne),
    Lp.coeFn_sub (rawProductSquare u v : GaussianL2)
      ((2 * inner ℝ u v) • (rawProduct u v : GaussianL2)),
    Lp.coeFn_smul (2 * inner ℝ u v) (rawProduct u v : GaussianL2),
    Lp.coeFn_smul ((inner ℝ u v)^2) gaussianOne, rawProductSquare_coeFn u v,
    rawProduct_coeFn u v, gaussianOne_coeFn,
    polynomialProductL2_coeFn (mixedPolynomial u v) (mixedPolynomial u v),
    mixedTarget_coeFn u v] with ω ha hs hm hc h2 hp h1 hq hmix
  change (((rawProductSquare u v : GaussianL2) - (2 * inner ℝ u v) • (rawProduct u v : GaussianL2)) +
    (inner ℝ u v)^2 • gaussianOne) ω =
      polynomialProductL2 (mixedPolynomial u v) (mixedPolynomial u v) ω
  rw [ha, Pi.add_apply, hs, Pi.sub_apply, hm, hc, Pi.smul_apply, Pi.smul_apply,
    h2, hp, h1, hq]
  change (mixedPolynomial u v : GaussianL2) ω = _ at hmix
  rw [hmix]
  simp only [smul_eq_mul]
  ring

theorem centeredProductSquare_energy (u v : CoefficientSpace) :
    ‖centeredProductSquare u v‖^2 =
      9 * (‖u‖^2)^2 * (‖v‖^2)^2 +
        42 * ‖u‖^2 * ‖v‖^2 * (inner ℝ u v)^2 + 9 * (inner ℝ u v)^4 := by
  have h22 : inner ℝ (rawProductSquare u v : GaussianL2) (rawProductSquare u v : GaussianL2) =
      9 * (‖u‖^2)^2 * (‖v‖^2)^2 +
        72 * ‖u‖^2 * ‖v‖^2 * (inner ℝ u v)^2 + 24 * (inner ℝ u v)^4 := by
    rw [real_inner_self_eq_norm_sq]
    exact rawProduct_fourth_moment u v
  have h11 : inner ℝ (rawProduct u v : GaussianL2) (rawProduct u v : GaussianL2) =
      ‖u‖^2 * ‖v‖^2 + 2 * (inner ℝ u v)^2 := by
    rw [real_inner_self_eq_norm_sq, rawProduct_variance]
  have h12 := (real_inner_comm (rawProductSquare u v : GaussianL2) (rawProduct u v : GaussianL2)).trans
    (rawProductSquare_raw_inner u v)
  have h02 := (real_inner_comm (rawProductSquare u v : GaussianL2) gaussianOne).trans
    (rawProductSquare_one_inner u v)
  have h01 := (real_inner_comm (rawProduct u v : GaussianL2) gaussianOne).trans
    (rawProduct_one_inner u v)
  rw [← real_inner_self_eq_norm_sq]
  simp only [centeredProductSquare, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    h22, h11, rawProductSquare_raw_inner, rawProductSquare_one_inner, rawProduct_one_inner,
    h12, h02, h01, GaussianDeterministicGraphCore.gaussianOne_inner_self]
  ring

theorem mixed_fourth_moment (u v : CoefficientSpace) :
    ‖(polynomialProduct (mixedPolynomial u v) (mixedPolynomial u v) : GaussianL2)‖^2 =
      9 * (‖u‖^2)^2 * (‖v‖^2)^2 +
        42 * ‖u‖^2 * ‖v‖^2 * (inner ℝ u v)^2 + 9 * (inner ℝ u v)^4 := by
  rw [← centeredProductSquare_eq, centeredProductSquare_energy]

theorem mixedTarget_variance (u v : CoefficientSpace) :
    ‖mixedTarget u v‖^2 = ‖u‖^2 * ‖v‖^2 + (inner ℝ u v)^2 := by
  have hn : ‖gaussianOne‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, GaussianDeterministicGraphCore.gaussianOne_inner_self]
  change ‖(rawProduct u v : GaussianL2) -
    inner ℝ u v • (GaussianQuadraticIncrement.oneCore : GaussianL2)‖^2 = _
  rw [GaussianQuadraticIncrement.oneCore_eq]
  rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hn,
    real_inner_smul_right, rawProduct_one_inner, rawProduct_variance]
  ring

/-- The entire deficit in the sharp bound is six times the squared Gram determinant. -/
theorem mixed_fourth_upper_deficit (u v : CoefficientSpace) :
    15 * (‖mixedTarget u v‖^2)^2 -
      ‖(polynomialProduct (mixedPolynomial u v) (mixedPolynomial u v) : GaussianL2)‖^2 =
        6 * (‖u‖^2 * ‖v‖^2 - (inner ℝ u v)^2)^2 := by
  rw [mixed_fourth_moment, mixedTarget_variance]
  ring

theorem mixed_fourth_upper_bound (u v : CoefficientSpace) :
    ‖(polynomialProduct (mixedPolynomial u v) (mixedPolynomial u v) : GaussianL2)‖^2 ≤
      15 * (‖mixedTarget u v‖^2)^2 := by
  have he := mixed_fourth_upper_deficit u v
  nlinarith [sq_nonneg (‖u‖^2 * ‖v‖^2 - (inner ℝ u v)^2)]

theorem mixed_fourth_upper_equality_iff (u v : CoefficientSpace) :
    ‖(polynomialProduct (mixedPolynomial u v) (mixedPolynomial u v) : GaussianL2)‖^2 =
      15 * (‖mixedTarget u v‖^2)^2 ↔ ‖u‖^2 * ‖v‖^2 = (inner ℝ u v)^2 := by
  have he := mixed_fourth_upper_deficit u v
  constructor
  · intro h
    rw [h, sub_self] at he
    have hz : (‖u‖^2 * ‖v‖^2 - (inner ℝ u v)^2)^2 = 0 := by linarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro h
    rw [h, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at he
    exact (sub_eq_zero.mp he).symm

theorem mixed_fourth_lower_bound (u v : CoefficientSpace) :
    9 * (‖mixedTarget u v‖^2)^2 ≤
      ‖(polynomialProduct (mixedPolynomial u v) (mixedPolynomial u v) : GaussianL2)‖^2 := by
  rw [mixed_fourth_moment, mixedTarget_variance]
  have hp : 0 ≤ ‖u‖^2 * ‖v‖^2 * (inner ℝ u v)^2 := by positivity
  nlinarith

end OperatorDerivativeRewrite.Foundation.GaussianMixedQuadraticFourthMoment
