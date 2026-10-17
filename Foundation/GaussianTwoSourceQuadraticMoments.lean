import Foundation.GaussianPureQuadraticProduct
import Foundation.FractionalControlledEstimate
import Foundation.GaussianObservedRecoveryHarmonicEnergy
import Foundation.GaussianLinearFieldDivergenceCompletion

/-! Exact moments of genuine two-source Gaussian products. Orthogonal products
give pure second chaos with fourth-moment ratio nine, distinct from rank one's fifteen. -/
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianTwoSourceQuadraticMoments
open InfiniteGaussian GaussianTimePolynomialPairing GaussianQuadraticIncrement
open GaussianQuarticWick GaussianNumberSectors GaussianQuadraticSourceHodge
open GaussianLinearFieldDivergenceCompletion GaussianDivergenceRecovery

def rawProduct (u v : CoefficientSpace) : polynomialCylindricalDomain :=
  polynomialProduct (firstChaosPolynomial u) (firstChaosPolynomial v)

theorem rawProduct_coeFn (u v : CoefficientSpace) :
    (rawProduct u v : GaussianL2) =ᵐ[gaussianProduct]
      fun ω => firstChaosEmbedding u ω * firstChaosEmbedding v ω := by
  filter_upwards [polynomialProductL2_coeFn (firstChaosPolynomial u) (firstChaosPolynomial v),
    firstChaosPolynomial_coeFn u, firstChaosPolynomial_coeFn v] with ω hp hu hv
  change polynomialProductL2 (firstChaosPolynomial u) (firstChaosPolynomial v) ω = _
  rw [hp, hu, hv]

theorem rawSquare_inner (u v : CoefficientSpace) :
    inner ℝ (FractionalControlledEstimate.square u) (FractionalControlledEstimate.square v) =
      ‖u‖^2 * ‖v‖^2 + 2 * (inner ℝ u v)^2 := by
  have hc (h : CoefficientSpace) : inner ℝ (centeredSquare h : GaussianL2) gaussianOne = 0 := by
    rw [real_inner_comm]
    exact centeredSquare_centered h
  simp only [FractionalControlledEstimate.square, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, centeredSquare_inner,
    centeredSquare_centered, hc, GaussianDeterministicGraphCore.gaussianOne_inner_self]
  ring

theorem rawProduct_variance (u v : CoefficientSpace) :
    ‖(rawProduct u v : GaussianL2)‖^2 = ‖u‖^2 * ‖v‖^2 + 2 * (inner ℝ u v)^2 := by
  have he : ‖(rawProduct u v : GaussianL2)‖^2 =
      inner ℝ (FractionalControlledEstimate.square u) (FractionalControlledEstimate.square v) := by
    rw [BochnerL2Dominated.norm_sq_integral, L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [rawProduct_coeFn u v, FractionalControlledEstimate.square_coeFn u,
      FractionalControlledEstimate.square_coeFn v] with ω hp hu hv
    rw [hp, hu, hv]
    simp only [Real.norm_eq_abs, sq_abs, Real.inner_apply]
    ring
  rw [he, rawSquare_inner]

theorem rawProduct_fourth_moment (u v : CoefficientSpace) :
    ‖(polynomialProduct (rawProduct u v) (rawProduct u v) : GaussianL2)‖^2 =
      9 * (‖u‖^2)^2 * (‖v‖^2)^2 +
        72 * ‖u‖^2 * ‖v‖^2 * (inner ℝ u v)^2 + 24 * (inner ℝ u v)^4 := by
  have he : ‖(polynomialProduct (rawProduct u v) (rawProduct u v) : GaussianL2)‖^2 =
      inner ℝ (quartic u) (quartic v) := by
    rw [BochnerL2Dominated.norm_sq_integral, L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [polynomialProductL2_coeFn (rawProduct u v) (rawProduct u v),
      rawProduct_coeFn u v, quartic_coeFn u, quartic_coeFn v] with ω hs hp hu hv
    change ‖polynomialProductL2 (rawProduct u v) (rawProduct u v) ω‖^2 = _
    rw [hs, hp, hu, hv]
    simp only [Real.norm_eq_abs, sq_abs, Real.inner_apply]
    ring
  rw [he, quartic_inner]

theorem orthogonal_rawProduct_second_chaos (u v : CoefficientSpace) (hc : inner ℝ u v = 0) :
    (rawProduct u v : GaussianL2) ∈ sector 2 := by
  have he : mixedTarget u v = (rawProduct u v : GaussianL2) := by
    change ((polynomialProduct (firstChaosPolynomial u) (firstChaosPolynomial v) -
      inner ℝ u v • oneCore : polynomialCylindricalDomain) : GaussianL2) = _
    simp only [hc, zero_smul, sub_zero]
    rfl
  rw [← he]
  exact mixedTarget_mem_sector_two u v

theorem orthogonal_rawProduct_fourth_ratio (u v : CoefficientSpace) (hc : inner ℝ u v = 0) :
    ‖(polynomialProduct (rawProduct u v) (rawProduct u v) : GaussianL2)‖^2 =
      9 * (‖(rawProduct u v : GaussianL2)‖^2)^2 := by
  rw [rawProduct_fourth_moment, rawProduct_variance, hc]
  ring

theorem orthogonal_rawProduct_recovery_energy (u v : CoefficientSpace) (hc : inner ℝ u v = 0) :
    ‖recovery (rawProduct u v)‖^2 = (1/2 : ℝ) * ‖u‖^2 * ‖v‖^2 := by
  have he := GaussianObservedRecoveryHarmonicEnergy.recovery_sector_energy
    ⟨(rawProduct u v : GaussianL2), orthogonal_rawProduct_second_chaos u v hc⟩
  change ‖recovery (rawProduct u v)‖^2 = (2 : ℝ)⁻¹ * ‖(rawProduct u v : GaussianL2)‖^2 at he
  rw [he, rawProduct_variance, hc]
  ring

end OperatorDerivativeRewrite.Foundation.GaussianTwoSourceQuadraticMoments
