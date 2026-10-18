import Foundation.IBMQuarticSecondChaos
import Foundation.GaussianQuadraticSourceHodge
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Bounded quadratic calculus for the actual centered first-chaos products.
The norm is derived by reusing verified source derivative/divergence graphs. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMQuadraticSpatialCalculus
open InfiniteGaussian IBMQuarticSecondChaos GaussianTimeSpaceHermite
open GaussianTimeFieldNorm GaussianQuadraticSourceHodge

theorem cross_eq_mixedTarget (u v : CoefficientSpace) : cross u v = mixedTarget u v := by
  apply Lp.ext
  exact (cross_coeFn u v).trans (mixedTarget_coeFn u v).symm

theorem cross_norm_sq (u v : CoefficientSpace) :
    ‖cross u v‖^2 = ‖u‖^2 * ‖v‖^2 + (inner ℝ u v)^2 := by
  have he := GaussianNumberSectors.graph_duality (mixed_derivative_graph u v)
    (mixed_divergence_graph u v)
  rw [inner_add_left, scalarTensor_pair_inner, scalarTensor_pair_inner,
    firstChaosEmbedding.inner_map_map, firstChaosEmbedding.inner_map_map,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_comm v u] at he
  rw [cross_eq_mixedTarget, ← real_inner_comm u v]
  nlinarith [he]

theorem cross_norm_le (u v : CoefficientSpace) : ‖cross u v‖ ≤ 2*‖u‖*‖v‖ := by
  have he := cross_norm_sq u v
  have hi := pow_le_pow_left₀ (norm_nonneg (inner ℝ u v))
    (norm_inner_le_norm (𝕜 := ℝ) u v) 2
  simp only [Real.norm_eq_abs, sq_abs, mul_pow] at hi
  nlinarith [norm_nonneg (cross u v), norm_nonneg u, norm_nonneg v,
    mul_nonneg (norm_nonneg u) (norm_nonneg v), sq_nonneg (‖u‖*‖v‖)]

theorem cross_comm (u v : CoefficientSpace) : cross u v = cross v u := by
  apply Lp.ext
  filter_upwards [cross_coeFn u v, cross_coeFn v u] with ω huv hvu
  rw [huv, hvu, real_inner_comm v u, mul_comm]

theorem cross_add_left (u v w : CoefficientSpace) : cross (u+v) w = cross u w + cross v w := by
  apply Lp.ext
  filter_upwards [cross_coeFn (u+v) w, cross_coeFn u w, cross_coeFn v w,
    Lp.coeFn_add (cross u w) (cross v w),
    Lp.coeFn_add (firstChaosEmbedding u) (firstChaosEmbedding v)] with ω hsum hu hv ha he
  rw [hsum, ha, Pi.add_apply, hu, hv, map_add, he, Pi.add_apply, inner_add_left]
  ring

theorem cross_add_right (u v w : CoefficientSpace) : cross u (v+w) = cross u v + cross u w := by
  rw [cross_comm, cross_add_left, cross_comm v u, cross_comm w u]

theorem cross_smul_right (a : ℝ) (u v : CoefficientSpace) : cross u (a • v) = a • cross u v := by
  rw [cross_comm, cross_smul_left, cross_comm v u]

def crossBilinear : CoefficientSpace →L[ℝ] CoefficientSpace →L[ℝ] GaussianL2 :=
  (LinearMap.mk₂ ℝ cross cross_add_left cross_smul_left cross_add_right cross_smul_right).mkContinuous₂
    2 cross_norm_le

theorem crossBilinear_apply (u v : CoefficientSpace) : crossBilinear u v = cross u v := rfl

theorem cross_hasDerivAt {u v : ℝ → CoefficientSpace} {u' v' : CoefficientSpace} {r : ℝ}
    (hu : HasDerivAt u u' r) (hv : HasDerivAt v v' r) :
    HasDerivAt (fun x => cross (u x) (v x)) (cross (u r) v' + cross u' (v r)) r := by
  exact ContinuousLinearMap.hasDerivAt_of_bilinear (B := crossBilinear) (fun _ => hu) (fun _ => hv)

theorem wickTwo_hasDerivAt {u : ℝ → CoefficientSpace} {u' : CoefficientSpace} {r : ℝ}
    (hu : HasDerivAt u u' r) :
    HasDerivAt (fun x => (wick (u x) 2 : GaussianL2)) ((2 : ℝ) • cross (u r) u') r := by
  have he := cross_hasDerivAt hu hu
  simpa only [cross_self, cross_comm u' (u r), ← two_smul ℝ] using he

end OperatorDerivativeRewrite.Foundation.IBMQuadraticSpatialCalculus
