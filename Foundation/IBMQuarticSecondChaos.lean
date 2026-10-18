import Foundation.IBMEvenCorrectionProjection
import Foundation.GaussianTerminalPredictionSpectrum
import Foundation.IBMFirstChaosMixedStein

/-! A genuine higher-source kernel test: the actual second-chaos projection
of the existing quartic correction. No Schwartz expansion is assumed. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticSecondChaos
open InfiniteGaussian GaussianTimeSpaceHermite GaussianQuarticWick
open GaussianNumberSectors IBMEvenCorrectionProjection IBMFirstChaosMixedStein

theorem wickTwo_coeFn (u : CoefficientSpace) :
    (wick u 2 : GaussianL2) =ᵐ[gaussianProduct]
      fun ω => (firstChaosEmbedding u ω)^2 - ‖u‖^2 := by
  simpa only [wick, value_two] using core_coeFn u (‖u‖^2) 2

def cross (u v : CoefficientSpace) : GaussianL2 :=
  (1/2 : ℝ) • ((wick (u+v) 2 : GaussianL2) - (wick u 2 : GaussianL2) - (wick v 2 : GaussianL2))

theorem cross_coeFn (u v : CoefficientSpace) :
    cross u v =ᵐ[gaussianProduct]
      fun ω => firstChaosEmbedding u ω * firstChaosEmbedding v ω - inner ℝ u v := by
  filter_upwards [Lp.coeFn_smul (1/2 : ℝ)
    ((wick (u+v) 2 : GaussianL2) - (wick u 2 : GaussianL2) - (wick v 2 : GaussianL2)),
    Lp.coeFn_sub ((wick (u+v) 2 : GaussianL2) - (wick u 2 : GaussianL2)) (wick v 2 : GaussianL2),
    Lp.coeFn_sub (wick (u+v) 2 : GaussianL2) (wick u 2 : GaussianL2),
    wickTwo_coeFn (u+v), wickTwo_coeFn u, wickTwo_coeFn v,
    Lp.coeFn_add (firstChaosEmbedding u) (firstChaosEmbedding v)] with ω hs hsub hsu ha hu hv he
  rw [cross, hs, Pi.smul_apply, hsub, Pi.sub_apply, hsu, Pi.sub_apply, ha, hu, hv,
    map_add, he, Pi.add_apply, norm_add_sq_real]
  simp only [smul_eq_mul]
  ring

theorem wickTwo_add (u v : CoefficientSpace) :
    (wick (u+v) 2 : GaussianL2) =
      (wick u 2 : GaussianL2) + (wick v 2 : GaussianL2) + (2 : ℝ) • cross u v := by
  unfold cross
  module

theorem wickTwo_sub (u v : CoefficientSpace) :
    (wick (u-v) 2 : GaussianL2) =
      (wick u 2 : GaussianL2) + (wick v 2 : GaussianL2) - (2 : ℝ) • cross u v := by
  apply Lp.ext
  filter_upwards [wickTwo_coeFn (u-v), wickTwo_coeFn u, wickTwo_coeFn v, cross_coeFn u v,
    Lp.coeFn_sub ((wick u 2 : GaussianL2)+(wick v 2 : GaussianL2)) ((2 : ℝ) • cross u v),
    Lp.coeFn_add (wick u 2 : GaussianL2) (wick v 2 : GaussianL2),
    Lp.coeFn_smul (2 : ℝ) (cross u v),
    Lp.coeFn_sub (firstChaosEmbedding u) (firstChaosEmbedding v)] with ω hm hu hv hc hs ha h2 he
  rw [hm, hs, Pi.sub_apply, ha, Pi.add_apply, h2, Pi.smul_apply, hu, hv, hc,
    map_sub, he, Pi.sub_apply, norm_sub_sq_real]
  simp only [smul_eq_mul]
  ring

theorem cross_smul_left (a : ℝ) (u v : CoefficientSpace) :
    cross (a • u) v = a • cross u v := by
  apply Lp.ext
  filter_upwards [cross_coeFn (a • u) v, cross_coeFn u v, Lp.coeFn_smul a (cross u v),
    Lp.coeFn_smul a (firstChaosEmbedding u)] with ω hc hu hs he
  rw [hc, hs, Pi.smul_apply, hu, map_smul, he, Pi.smul_apply, real_inner_smul_left]
  simp only [smul_eq_mul]
  ring

theorem quartic_projection_two (u : CoefficientSpace) :
    projection 2 (quartic u) = (6*‖u‖^2 : ℝ) • (wick u 2 : GaussianL2) := by
  simp only [quartic, map_add, map_smul, GaussianTerminalPredictionSpectrum.projection_wick]
  norm_num

theorem squareProduct_projection_two (u v : CoefficientSpace) :
    projection 2 (squareProduct u v) =
      ‖v‖^2 • (wick u 2 : GaussianL2) + ‖u‖^2 • (wick v 2 : GaussianL2) +
        (4*inner ℝ u v) • cross u v := by
  simp only [squareProduct, map_smul, map_sub, map_add, quartic_projection_two]
  rw [norm_add_sq_real, norm_sub_sq_real, wickTwo_add, wickTwo_sub]
  module

theorem cubeProduct_projection_two (u w : CoefficientSpace) :
    projection 2 (cubeProduct u w) =
      (3*‖u‖^2 : ℝ) • cross u w + (3*inner ℝ u w) • (wick u 2 : GaussianL2) := by
  simp only [cubeProduct, map_smul, map_sub, map_add, quartic_projection_two]
  rw [norm_add_sq_real, norm_sub_sq_real, norm_add_sq_real, norm_sub_sq_real,
    wickTwo_add, wickTwo_sub, wickTwo_add, wickTwo_sub,
    cross_smul_left, wick_two_smul, real_inner_smul_left]
  simp only [norm_smul, Real.norm_eq_abs]
  norm_num
  module

/-- This is the actual polynomial correction's second source projection.
It is a finite exact channel test, not the general Schwartz theorem. -/
theorem quarticCorrection_projection_two (u v w : CoefficientSpace) :
    projection 2 (quarticCorrection u v w) =
      ((‖v‖^2 + inner ℝ u w)/2) • (wick u 2 : GaussianL2) +
      (2*inner ℝ u v) • cross u v +
      (‖u‖^2/2) • ((wick v 2 : GaussianL2) + cross u w) := by
  rw [quarticCorrection, map_add, map_smul, map_smul,
    squareProduct_projection_two, cubeProduct_projection_two]
  module

theorem cross_self (u : CoefficientSpace) : cross u u = (wick u 2 : GaussianL2) := by
  apply Lp.ext
  filter_upwards [cross_coeFn u u, wickTwo_coeFn u] with ω hc hw
  rw [hc, hw, real_inner_self_eq_norm_sq, pow_two]
  ring

/-- A nonzero second-source channel can coexist with the exactly vanishing
first-source channel already proved for this even polynomial correction. -/
theorem quartic_second_energy_test (u : CoefficientSpace) (hu : ‖u‖^2 = 1) :
    ‖projection 2 (quarticCorrection u u u)‖^2 = 32 := by
  rw [quarticCorrection_projection_two, cross_self, real_inner_self_eq_norm_sq, hu]
  have he : ((1 + (1 : ℝ))/2) • (wick u 2 : GaussianL2) +
      (2*(1 : ℝ)) • (wick u 2 : GaussianL2) +
      ((1 : ℝ)/2) • ((wick u 2 : GaussianL2)+(wick u 2 : GaussianL2)) =
      (4 : ℝ) • (wick u 2 : GaussianL2) := by module
  rw [he, norm_smul, mul_pow, GaussianWickContinuity.wick_norm_sq, hu]
  norm_num

end OperatorDerivativeRewrite.Foundation.IBMQuarticSecondChaos
