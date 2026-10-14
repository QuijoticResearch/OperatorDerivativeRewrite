import Foundation.IBMCubicFirstChaos

/-! Parity of the zero-shift quartic IBM spatial correction, proved using
actual even Wick components and the existing first-chaos projection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory

namespace OperatorDerivativeRewrite.Foundation.IBMEvenCorrectionProjection
open InfiniteGaussian GaussianTimeSpaceHermite GaussianQuarticWick IBMCubicFirstChaos

theorem adjoint_quartic (u : CoefficientSpace) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (quartic u) = 0 := by
  apply ext_inner_right ℝ
  intro k
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (quartic u) (firstChaosEmbedding k) = _
  rw [← wick_one_eq_embedding]
  simp only [quartic, inner_add_left, real_inner_smul_left, wick_inner]
  norm_num

def squareProduct (u v : CoefficientSpace) : GaussianL2 :=
  (1/12 : ℝ) • (quartic (u+v) + quartic (u-v) - (2 : ℝ)•quartic u - (2 : ℝ)•quartic v)

theorem squareProduct_coeFn (u v : CoefficientSpace) :
    squareProduct u v =ᵐ[gaussianProduct]
      fun ω => (firstChaosEmbedding u ω)^2*(firstChaosEmbedding v ω)^2 := by
  filter_upwards [Lp.coeFn_smul (1/12 : ℝ)
      (quartic (u+v)+quartic (u-v)-(2 : ℝ)•quartic u-(2 : ℝ)•quartic v),
    Lp.coeFn_sub (quartic (u+v)+quartic (u-v)-(2 : ℝ)•quartic u) ((2 : ℝ)•quartic v),
    Lp.coeFn_sub (quartic (u+v)+quartic (u-v)) ((2 : ℝ)•quartic u),
    Lp.coeFn_add (quartic (u+v)) (quartic (u-v)),
    Lp.coeFn_smul (2 : ℝ) (quartic u), Lp.coeFn_smul (2 : ℝ) (quartic v),
    quartic_coeFn (u+v), quartic_coeFn (u-v), quartic_coeFn u, quartic_coeFn v,
    Lp.coeFn_add (firstChaosEmbedding u) (firstChaosEmbedding v),
    Lp.coeFn_sub (firstChaosEmbedding u) (firstChaosEmbedding v)]
      with ω hs hd1 hd2 ha hu hv hp hm hqu hqv he1 he2
  rw [squareProduct, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hd1]
  simp only [Pi.sub_apply]
  rw [hd2]
  simp only [Pi.sub_apply]
  rw [ha, hu, hv]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp, hm, hqu, hqv]
  rw [map_add, map_sub, he1, he2]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

def cubeProduct (u w : CoefficientSpace) : GaussianL2 :=
  (1/48 : ℝ) • (quartic ((2 : ℝ)•u+w)-quartic ((2 : ℝ)•u-w) -
    (2 : ℝ)•quartic (u+w) + (2 : ℝ)•quartic (u-w))

theorem cubeProduct_coeFn (u w : CoefficientSpace) :
    cubeProduct u w =ᵐ[gaussianProduct]
      fun ω => (firstChaosEmbedding u ω)^3*firstChaosEmbedding w ω := by
  filter_upwards [Lp.coeFn_smul (1/48 : ℝ)
      (quartic ((2 : ℝ)•u+w)-quartic ((2 : ℝ)•u-w)-(2 : ℝ)•quartic (u+w)+(2 : ℝ)•quartic (u-w)),
    Lp.coeFn_add (quartic ((2 : ℝ)•u+w)-quartic ((2 : ℝ)•u-w)-(2 : ℝ)•quartic (u+w))
      ((2 : ℝ)•quartic (u-w)),
    Lp.coeFn_sub (quartic ((2 : ℝ)•u+w)-quartic ((2 : ℝ)•u-w)) ((2 : ℝ)•quartic (u+w)),
    Lp.coeFn_sub (quartic ((2 : ℝ)•u+w)) (quartic ((2 : ℝ)•u-w)),
    Lp.coeFn_smul (2 : ℝ) (quartic (u+w)), Lp.coeFn_smul (2 : ℝ) (quartic (u-w)),
    quartic_coeFn ((2 : ℝ)•u+w), quartic_coeFn ((2 : ℝ)•u-w), quartic_coeFn (u+w),
    quartic_coeFn (u-w), Lp.coeFn_add (firstChaosEmbedding ((2 : ℝ)•u)) (firstChaosEmbedding w),
    Lp.coeFn_sub (firstChaosEmbedding ((2 : ℝ)•u)) (firstChaosEmbedding w),
    Lp.coeFn_smul (2 : ℝ) (firstChaosEmbedding u),
    Lp.coeFn_add (firstChaosEmbedding u) (firstChaosEmbedding w),
    Lp.coeFn_sub (firstChaosEmbedding u) (firstChaosEmbedding w)]
      with ω hs ha hd1 hd2 h2p h2m hqp hqm hpu hmu he1 he2 he3 he4 he5
  rw [cubeProduct, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ha]
  simp only [Pi.add_apply]
  rw [hd1]
  simp only [Pi.sub_apply]
  rw [hd2]
  simp only [Pi.sub_apply]
  rw [h2p, h2m]
  simp only [Pi.smul_apply, smul_eq_mul, hqp, hqm, hpu, hmu]
  rw [map_add, map_sub, map_add, map_sub, he1, he2]
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [map_smul, he3, he4, he5]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

def quarticCorrection (u v w : CoefficientSpace) : GaussianL2 :=
  (1/2 : ℝ)•squareProduct u v + (1/6 : ℝ)•cubeProduct u w

theorem quarticCorrection_coeFn (u v w : CoefficientSpace) :
    quarticCorrection u v w =ᵐ[gaussianProduct] fun ω =>
      (1/2 : ℝ)*(firstChaosEmbedding u ω)^2*(firstChaosEmbedding v ω)^2 +
        (1/6 : ℝ)*(firstChaosEmbedding u ω)^3*firstChaosEmbedding w ω := by
  filter_upwards [Lp.coeFn_add ((1/2 : ℝ)•squareProduct u v) ((1/6 : ℝ)•cubeProduct u w),
    Lp.coeFn_smul (1/2 : ℝ) (squareProduct u v), Lp.coeFn_smul (1/6 : ℝ) (cubeProduct u w),
    squareProduct_coeFn u v, cubeProduct_coeFn u w] with ω ha hs1 hs2 h1 h2
  rw [quarticCorrection, ha]
  simp only [Pi.add_apply, hs1, hs2, Pi.smul_apply, smul_eq_mul, h1, h2]
  ring

/-- Nonzero zeroth-chaos expectation is compatible with exactly zero first
chaos for the zero-shift quartic test. -/
theorem quarticCorrection_projection_zero (u v w : CoefficientSpace) :
    GaussianPastFirstChaos.projection (quarticCorrection u v w) = 0 := by
  change firstChaosEmbedding (firstChaosEmbedding.toContinuousLinearMap.adjoint (quarticCorrection u v w)) = 0
  simp only [quarticCorrection, squareProduct, cubeProduct, map_add, map_sub,
    map_smul, adjoint_quartic, smul_zero, add_zero, sub_zero, map_zero]

end OperatorDerivativeRewrite.Foundation.IBMEvenCorrectionProjection
