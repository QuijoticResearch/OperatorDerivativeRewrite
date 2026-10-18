import Foundation.IBMGaussianMeanDerivative

/-! The genuine nonlinear Schwartz second-source primitive and its spatial
derivatives, connected to the constructed mollified curvature. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzSpatialPrimitive
open InfiniteGaussian GaussianTimeSpaceHermite GaussianNumberSectors
open IBMCorrectionStein IBMShiftedJetMoments IBMGaussianMeanDerivative
open IBMQuarticSecondChaos IBMQuadraticSpatialCalculus IBMSchwartzSecondProjection

def primitive (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) : GaussianL2 :=
  (M g a u 2 0/2) • (wick u 2 : GaussianL2)

def slope (g : SchwartzMap ℝ ℝ) (a : ℝ) (u v : CoefficientSpace) : GaussianL2 :=
  (inner ℝ u v*M g a u 4 0/2) • (wick u 2 : GaussianL2) + M g a u 2 0 • cross u v

theorem primitive_eq_projection (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) :
    primitive g a u = projection 2
      (IBMFirstChaosMixedStein.testClass u (shiftedJet_smooth g a 0).continuous
        (shiftedJet_bound g a 0)) := by
  rw [IBMScalarSecondProjection.shiftedJet_projection_two, primitive, moment_zero]
  congr 1
  ring

theorem primitive_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ)
    {u : ℝ → CoefficientSpace} {v : CoefficientSpace} {r : ℝ} (hu : HasDerivAt u v r) :
    HasDerivAt (fun x => primitive g a (u x)) (slope g a (u r) v) r := by
  have hq := mean_comp_hasDerivAt g a 2 hu
  have hw := wickTwo_hasDerivAt hu
  have he := (hq.div_const 2).smul hw
  convert he using 1
  · rfl
  · unfold slope
    module

theorem slope_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ)
    {u v : ℝ → CoefficientSpace} {w : CoefficientSpace} {r : ℝ}
    (hu : HasDerivAt u (v r) r) (hv : HasDerivAt v w r) :
    HasDerivAt (fun x => slope g a (u x) (v x)) (secondCandidate g a (u r) (v r) w) r := by
  have h2 := mean_comp_hasDerivAt g a 2 hu
  have h4 := mean_comp_hasDerivAt g a 4 hu
  have hd := hu.inner ℝ hv
  have hw := wickTwo_hasDerivAt hu
  have hx := cross_hasDerivAt hu hv
  have he := (((hd.mul h4).div_const 2).smul hw).add (h2.smul hx)
  convert he using 1
  · rfl
  · simp only [Pi.mul_apply, real_inner_self_eq_norm_sq, cross_self]
    unfold secondCandidate
    module

def spatialPrimitive (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) : GaussianL2 :=
  primitive g a (IBMGaussianSteinMoments.tripleCoefficient n r 0)

def spatialSlope (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) : GaussianL2 :=
  slope g a (IBMGaussianSteinMoments.tripleCoefficient n r 0)
    (IBMGaussianSteinMoments.tripleCoefficient n r 1)

theorem spatialPrimitive_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (spatialPrimitive g a n) (spatialSlope g a n r) r :=
  primitive_hasDerivAt g a (IBMQuarticSecondPrimitive.coefficient_zero_hasDerivAt n r)

theorem spatialSlope_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (spatialSlope g a n) (projection 2 (mollifiedClass g a n r)) r := by
  rw [mollified_projection_two]
  exact slope_hasDerivAt g a (IBMQuarticSecondPrimitive.coefficient_zero_hasDerivAt n r)
    (IBMQuarticSecondPrimitive.coefficient_one_hasDerivAt n r)

/-- Literal Gaussian-L2 second derivative of a projected actual Schwartz
observable, equal to the projection of the actual field curvature. -/
theorem spatialPrimitive_second_deriv (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    deriv (deriv (spatialPrimitive g a n)) r = projection 2 (mollifiedClass g a n r) := by
  have he : deriv (spatialPrimitive g a n) = spatialSlope g a n :=
    funext fun x => (spatialPrimitive_hasDerivAt g a n x).deriv
  rw [he]
  exact (spatialSlope_hasDerivAt g a n r).deriv

theorem spatialSlope_eq_origin_projection (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    spatialSlope g a n r = projection 2 (weightedClass g a
      (IBMGaussianSteinMoments.tripleCoefficient n r 0) 1
      (firstChaosEmbedding (IBMGaussianSteinMoments.tripleCoefficient n r 1))) := by
  rw [weighted_linear_projection]
  unfold spatialSlope slope
  norm_num
  exact add_comm _ _

end OperatorDerivativeRewrite.Foundation.IBMSchwartzSpatialPrimitive
