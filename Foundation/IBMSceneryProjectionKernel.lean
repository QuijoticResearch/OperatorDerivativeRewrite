import Foundation.IBMSceneryCubicProjection

/-! Explicit, integrable Bochner source kernel for the finite-mollifier
cubic first chaos. The source is the verified Brownian spectral Hilbert space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory

namespace OperatorDerivativeRewrite.Foundation.IBMSceneryProjectionKernel
open IBMSceneryCubicProjection IBMContinuousScenery IBMJointMollifierGaussian
open FractionalSpectralKernel IBMFiniteScenerySmoothing
open IBMMollifier
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

def weight (n : ℕ) (x r : ℝ) : ℝ :=
  ((1/2 : ℝ)*deriv (fun y => deriv (wholeLineVariance (IBMMollifier.kernel n)) y) x)*
      IBMMollifier.kernel n (x-r) +
    deriv (wholeLineVariance (IBMMollifier.kernel n)) x*deriv (IBMMollifier.kernel n) (x-r) +
    ((1/2 : ℝ)*wholeLineVariance (IBMMollifier.kernel n) x)*
      deriv (deriv (IBMMollifier.kernel n)) (x-r)

theorem weighted_direction_integrable (n : ℕ) (i : Fin 3) (x : ℝ) :
    Integrable (fun r => derivativeKernel n i (x-r) • direction r) volume := by
  have hr := IBMDyadicExtension.derivativeKernel_regular n i
  exact direction_continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
    (hr.2.continuous.comp (continuous_const.sub continuous_id))
    (hr.1.comp_homeomorph (Homeomorph.subLeft x))

theorem sourceVector_eq_integral (n : ℕ) (x : ℝ) :
    sourceVector n x = ∫ r, weight n x r • direction r := by
  have hi0 := weighted_direction_integrable n 0 x
  have hi1 := weighted_direction_integrable n 1 x
  have hi2 := weighted_direction_integrable n 2 x
  simp only [derivativeKernel, Fin.isValue, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    if_neg, if_pos, ite_false, ite_true] at hi0 hi1 hi2
  unfold sourceVector wholeLineDirection
  rw [← integral_smul, ← integral_smul, ← integral_smul]
  have h0 := hi0.smul ((1/2 : ℝ)*deriv (fun y => deriv (wholeLineVariance (kernel n)) y) x)
  have h1 := hi1.smul (deriv (wholeLineVariance (kernel n)) x)
  have h2 := hi2.smul ((1/2 : ℝ)*wholeLineVariance (kernel n) x)
  have he01 := integral_add h0 h1
  have he012 := integral_add (h0.add h1) h2
  simp only [Pi.smul_apply, Pi.add_apply] at he01 he012
  rw [← he01, ← he012]
  congr 1
  funext r
  simp only [weight, Pi.add_apply, Pi.smul_apply, add_smul, smul_smul, smul_eq_mul]

theorem projection_eq_integrated_source_kernel (n : ℕ) (x : ℝ) :
    GaussianPastFirstChaos.projection (spatialCorrection n x) =
      GaussianHilbertProcess.isonormalEmbedding SpectralSpace
        (∫ r, weight n x r • direction r) := by
  rw [projection_eq_sourceEmbedding, sourceVector_eq_integral]

/-- The explicit integrated kernel is exactly the mean of the actual closed
source derivative, after the repository's constructed Hilbert isometry. -/
theorem mean_source_derivative_eq_kernel (n : ℕ) (x : ℝ) :
    (∫ ω, InfiniteGaussian.polynomialDerivative
      (IBMCubicFirstChaos.correctionCore
        (IBMGaussianSteinMoments.tripleCoefficient n x 0)
        (IBMGaussianSteinMoments.tripleCoefficient n x 1)
        (IBMGaussianSteinMoments.tripleCoefficient n x 2)) ω
      ∂InfiniteGaussian.gaussianProduct) =
    SeparableHilbertEmbedding.hilbertEmbedding SpectralSpace
      (∫ r, weight n x r • direction r) := by
  rw [IBMCubicFirstChaos.mean_derivative_correction]
  apply InfiniteGaussian.firstChaosEmbedding.injective
  rw [← IBMCubicFirstChaos.projection_correction]
  exact projection_eq_integrated_source_kernel n x

end OperatorDerivativeRewrite.Foundation.IBMSceneryProjectionKernel
