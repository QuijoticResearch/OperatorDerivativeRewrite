import Foundation.IBMCubicFirstChaos
import Foundation.IBMNegativeBulkVariance
import Foundation.IBMFiniteHorizonEvaluation

/-! The exact first-chaos projection of the actual mollified scenery's cubic
spatial correction, retaining the origin variance geometry. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMSceneryCubicProjection
open InfiniteGaussian IBMCubicFirstChaos IBMGaussianSteinMoments IBMJointMollifierGaussian
open IBMContinuousScenery IBMMollifier FractionalSpectralKernel SeparableHilbertEmbedding
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable
attribute [local irreducible] IBMDyadicExtension.field

def spatialCorrection (n : ℕ) (x : ℝ) : GaussianL2 :=
  correction (tripleCoefficient n x 0) (tripleCoefficient n x 1) (tripleCoefficient n x 2)

theorem spatialCorrection_coeFn (n : ℕ) (x : ℝ) :
    spatialCorrection n x =ᵐ[gaussianProduct] fun ω =>
      IBMDyadicExtension.field n 0 ω x*(IBMDyadicExtension.field n 1 ω x)^2 +
        (1/2 : ℝ)*(IBMDyadicExtension.field n 0 ω x)^2*IBMDyadicExtension.field n 2 ω x := by
  filter_upwards [correction_coeFn (tripleCoefficient n x 0) (tripleCoefficient n x 1)
      (tripleCoefficient n x 2), IBMDyadicExtension.field_coordinate_ae n 0 x,
    IBMDyadicExtension.field_coordinate_ae n 1 x, IBMDyadicExtension.field_coordinate_ae n 2 x]
      with ω h h0 h1 h2
  rw [h0, h1, h2]
  exact h

theorem spatialCorrection_projection (n : ℕ) (x : ℝ) :
    GaussianPastFirstChaos.projection (spatialCorrection n x) =
      (cov[gaussianTriple n x 1, gaussianTriple n x 1; gaussianProduct] +
        cov[gaussianTriple n x 0, gaussianTriple n x 2; gaussianProduct]) •
          wholeLineScenery (kernel n) x +
      (2*cov[gaussianTriple n x 0, gaussianTriple n x 1; gaussianProduct]) •
          wholeLineScenery (deriv (kernel n)) x +
      ((1/2 : ℝ)*cov[gaussianTriple n x 0, gaussianTriple n x 0; gaussianProduct]) •
          wholeLineScenery (deriv (deriv (kernel n))) x := by
  rw [spatialCorrection, projection_correction]
  simp only [coefficient, map_add, map_smul]
  have he (i : Fin 3) : firstChaosEmbedding (tripleCoefficient n x i) =
      wholeLineScenery (derivativeKernel n i) x := (wholeLineScenery_eq_sourceEmbedding _ _).symm
  simp_rw [← real_inner_self_eq_norm_sq, tripleCoefficient_inner, he]
  simp [derivativeKernel]

theorem positive_bulk_projection (n : ℕ) (x : ℝ) (hbulk : (bump n).rOut < x) :
    GaussianPastFirstChaos.projection (spatialCorrection n x) =
      wholeLineScenery (deriv (kernel n)) x +
      ((1/2 : ℝ)*wholeLineVariance (kernel n) x) •
        wholeLineScenery (deriv (deriv (kernel n))) x := by
  rw [spatialCorrection_projection, gaussianTriple_interior_covariance_cancellation n x hbulk,
    gaussianTriple_interior_covariance_half n x hbulk,
    gaussianTriple_covariance_eq_L2_inner]
  simp [derivativeKernel, wholeLineVariance, real_inner_self_eq_norm_sq]

/-- The negative exterior has the opposite V coefficient. -/
theorem negative_bulk_projection (n : ℕ) (x : ℝ) (hbulk : x < -(bump n).rOut) :
    GaussianPastFirstChaos.projection (spatialCorrection n x) =
      -wholeLineScenery (deriv (kernel n)) x +
      ((1/2 : ℝ)*wholeLineVariance (kernel n) x) •
        wholeLineScenery (deriv (deriv (kernel n))) x := by
  rw [spatialCorrection_projection]
  simp_rw [gaussianTriple_covariance_eq_L2_inner]
  simp only [derivativeKernel, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    if_neg, if_pos, ite_false, ite_true, real_inner_self_eq_norm_sq]
  rw [IBMNegativeBulkVariance.concrete_negative_covariance_cancellation n x hbulk,
    IBMNegativeBulkVariance.concrete_negative_cross_covariance n x hbulk]
  norm_num [wholeLineVariance]

/-- Exact all-point variance geometry, including the finite origin layer.
No boundary term is dropped and no distributional limit is claimed. -/
theorem variance_geometry_projection (n : ℕ) (x : ℝ) :
    GaussianPastFirstChaos.projection (spatialCorrection n x) =
      ((1/2 : ℝ)*deriv (fun y => deriv (wholeLineVariance (kernel n)) y) x) •
        wholeLineScenery (kernel n) x +
      deriv (wholeLineVariance (kernel n)) x • wholeLineScenery (deriv (kernel n)) x +
      ((1/2 : ℝ)*wholeLineVariance (kernel n) x) •
        wholeLineScenery (deriv (deriv (kernel n))) x := by
  rw [spatialCorrection_projection]
  simp_rw [gaussianTriple_covariance_eq_L2_inner]
  simp only [derivativeKernel, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    if_neg, if_pos, ite_false, ite_true, real_inner_self_eq_norm_sq]
  rw [wholeLineVariance_deriv (kernel n) (kernel_compactSupport n)
      ((kernel_smooth n).of_le (by norm_num)),
    wholeLineVariance_second_deriv (kernel n) (kernel_compactSupport n)
      ((kernel_smooth n).of_le (by norm_num))]
  simp [wholeLineVariance]

def sourceVector (n : ℕ) (x : ℝ) : SpectralSpace :=
  ((1/2 : ℝ)*deriv (fun y => deriv (wholeLineVariance (kernel n)) y) x) •
      wholeLineDirection (kernel n) x +
    deriv (wholeLineVariance (kernel n)) x • wholeLineDirection (deriv (kernel n)) x +
    ((1/2 : ℝ)*wholeLineVariance (kernel n) x) • wholeLineDirection (deriv (deriv (kernel n))) x

/-- A concrete first-chaos source Hilbert vector of the actual scenery
correction. SpectralSpace is retained; it is not silently identified with the
manuscript's physical white-noise L²(dw) space. -/
theorem projection_eq_sourceEmbedding (n : ℕ) (x : ℝ) :
    GaussianPastFirstChaos.projection (spatialCorrection n x) =
      GaussianHilbertProcess.isonormalEmbedding SpectralSpace (sourceVector n x) := by
  rw [variance_geometry_projection]
  simp only [sourceVector, map_add, map_smul, wholeLineScenery_eq_sourceEmbedding]

end OperatorDerivativeRewrite.Foundation.IBMSceneryCubicProjection
