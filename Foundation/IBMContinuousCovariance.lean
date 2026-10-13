import Foundation.IBMContinuousScenery

/-! Exact continuous-kernel covariance and energy for the verified Brownian scenery.
These identities concern Gaussian L² Bochner integrals, without a pathwise modification. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
open InfiniteGaussian FractionalSpectralKernel FractionalSpectralGeometry
open GaussianHilbertProcess IBMFiniteScenerySmoothing
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

/-- The exact covariance geometry of two continuous compact-kernel averages. -/
theorem kernelDirection_inner_kernel (a b c d x y : ℝ)
    {ρ σ : ℝ → ℝ} (hρ : Continuous ρ) (hσ : Continuous σ) :
    inner ℝ (kernelDirection a b x ρ) (kernelDirection c d y σ) =
      ∫ s in Set.Icc c d, σ (y - s) *
        (∫ r in Set.Icc a b, ρ (x - r) * covariance (1/2) s r) := by
  change inner ℝ (kernelDirection a b x ρ)
    (∫ s in Set.Icc c d, σ (y - s) • direction s) = _
  rw [← integral_inner (weightedDirection_integrableOn c d y hσ)]
  congr 1
  funext s
  rw [real_inner_smul_right]
  rw [real_inner_comm, direction_inner_kernel a b x s hρ]

/-- The actual Gaussian cross moment of two compact-kernel Bochner averages
is the double integral of the Brownian covariance kernel. -/
theorem kernelScenery_cross_moment (a b c d x y : ℝ)
    {ρ σ : ℝ → ℝ} (hρ : Continuous ρ) (hσ : Continuous σ) :
    (∫ ω, isonormal SpectralSpace (kernelDirection a b x ρ) ω *
      isonormal SpectralSpace (kernelDirection c d y σ) ω ∂gaussianProduct) =
      ∫ s in Set.Icc c d, σ (y - s) *
        (∫ r in Set.Icc a b, ρ (x - r) * covariance (1/2) s r) := by
  rw [isonormal_product_integral]
  exact kernelDirection_inner_kernel a b c d x y hρ hσ

/-- Exact Gaussian L² energy of a continuous compact-kernel convolution. -/
theorem kernelScenery_energy (a b x : ℝ) {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    ‖kernelScenery a b x ρ‖ ^ 2 =
      ∫ s in Set.Icc a b, ρ (x - s) *
        (∫ r in Set.Icc a b, ρ (x - r) * covariance (1/2) s r) := by
  rw [kernelScenery_norm]
  rw [← real_inner_self_eq_norm_sq]
  exact kernelDirection_inner_kernel a b a b x x hρ hρ

end OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
