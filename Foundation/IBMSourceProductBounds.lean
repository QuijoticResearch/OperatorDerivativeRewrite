import Foundation.IBMSchwartzSourceDerivative
import Foundation.GaussianCubicGrowth

/-! Actual Gaussian products with separate homogeneous norm bounds, for
operator-norm differentiation of the full nonlinear source derivative. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMSourceProductBounds
open InfiniteGaussian IBMSchwartzSourceContinuity IBMQuarticSecondChaos
open IBMQuadraticSpatialCalculus IBMCubicFirstChaos

theorem rawProduct_eq_cross (u v : CoefficientSpace) :
    rawProduct u v = cross u v+inner ℝ u v • gaussianOne := by
  apply Lp.ext
  filter_upwards [rawProduct_coeFn u v, cross_coeFn u v,
    Lp.coeFn_add (cross u v) (inner ℝ u v • gaussianOne),
    Lp.coeFn_smul (inner ℝ u v) gaussianOne, gaussianOne_coeFn] with ω hr hc ha hs h1
  rw [hr, ha, Pi.add_apply, hc, hs, Pi.smul_apply, h1, smul_eq_mul]
  ring

theorem rawProduct_norm_le (u v : CoefficientSpace) : ‖rawProduct u v‖ ≤ 3*‖u‖*‖v‖ := by
  rw [rawProduct_eq_cross]
  have h := norm_add_le (cross u v) (inner ℝ u v • gaussianOne)
  have hone : ‖gaussianOne‖ = 1 := by
    have he := GaussianDeterministicGraphCore.gaussianOne_inner_self
    rw [real_inner_self_eq_norm_sq] at he
    nlinarith [norm_nonneg gaussianOne]
  simp only [norm_smul, hone, mul_one] at h
  have hi := norm_inner_le_norm (𝕜 := ℝ) u v
  have hc := cross_norm_le u v
  linarith

theorem rawProduct_comm (u v : CoefficientSpace) : rawProduct u v = rawProduct v u := by
  simp only [rawProduct_eq_cross, cross_comm u v, real_inner_comm u v]

theorem rawProduct_add_left (u v w : CoefficientSpace) :
    rawProduct (u+v) w = rawProduct u w+rawProduct v w := by
  simp only [rawProduct_eq_cross, cross_add_left, inner_add_left, add_smul]
  abel

theorem rawProduct_smul_left (c : ℝ) (u v : CoefficientSpace) :
    rawProduct (c • u) v = c • rawProduct u v := by
  simp only [rawProduct_eq_cross, cross_smul_left, real_inner_smul_left, smul_add, mul_smul]

theorem rawProduct_add_right (u v w : CoefficientSpace) :
    rawProduct u (v+w) = rawProduct u v+rawProduct u w := by
  rw [rawProduct_comm, rawProduct_add_left, rawProduct_comm v u, rawProduct_comm w u]

theorem rawProduct_smul_right (c : ℝ) (u v : CoefficientSpace) :
    rawProduct u (c • v) = c • rawProduct u v := by
  rw [rawProduct_comm, rawProduct_smul_left, rawProduct_comm v u]

def rawBilinear : CoefficientSpace →L[ℝ] CoefficientSpace →L[ℝ] GaussianL2 :=
  (LinearMap.mk₂ ℝ rawProduct rawProduct_add_left rawProduct_smul_left
    rawProduct_add_right rawProduct_smul_right).mkContinuous₂ 3 rawProduct_norm_le

theorem rawBilinear_apply (u v : CoefficientSpace) : rawBilinear u v = rawProduct u v := rfl

theorem mixedCube_smul (c d : ℝ) (u v : CoefficientSpace) :
    mixedCube (c • u) (d • v) = (c*d^2) • mixedCube u v := by
  apply Lp.ext
  filter_upwards [mixedCube_coeFn (c • u) (d • v), mixedCube_coeFn u v,
    Lp.coeFn_smul (c*d^2) (mixedCube u v), Lp.coeFn_smul c (firstChaosEmbedding u),
    Lp.coeFn_smul d (firstChaosEmbedding v)] with ω hm hu hs hc hd
  rw [hm, hs, Pi.smul_apply, hu, map_smul, hc, Pi.smul_apply,
    map_smul, hd, Pi.smul_apply]
  simp only [smul_eq_mul]
  ring

/-- Separate homogeneity, with a uniform constant for every direction,
including the zero directions. This is not bounded L2 multiplication. -/
theorem mixedCube_norm_separate (u v : CoefficientSpace) :
    ‖mixedCube u v‖ ≤ 12*‖u‖*‖v‖^2 := by
  by_cases hu : u=0
  · subst u
    simpa only [zero_smul, one_smul, zero_mul, mul_zero, norm_zero] using
      le_of_eq (congrArg norm (mixedCube_smul 0 1 (0 : CoefficientSpace) v))
  by_cases hv : v=0
  · subst v
    have hz := mixedCube_smul 1 0 u (0 : CoefficientSpace)
    simpa using le_of_eq (congrArg norm hz)
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u0 := ‖u‖⁻¹ • u
  let v0 := ‖v‖⁻¹ • v
  have hu0 : ‖u0‖ = 1 := by simp [u0, norm_smul, inv_mul_cancel₀ hnu.ne']
  have hv0 : ‖v0‖ = 1 := by simp [v0, norm_smul, inv_mul_cancel₀ hnv.ne']
  have hb := GaussianCubicGrowth.mixedCube_norm_le u0 v0 1 (by norm_num) hu0.le hv0.le
  have he : mixedCube u v = (‖u‖*‖v‖^2) • mixedCube u0 v0 := by
    rw [← mixedCube_smul]
    simp only [u0, v0, smul_smul, mul_inv_cancel₀ hnu.ne', mul_inv_cancel₀ hnv.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (‖u‖*‖v‖^2)*12 := mul_le_mul_of_nonneg_left (by simpa using hb) (by positivity)
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.IBMSourceProductBounds
