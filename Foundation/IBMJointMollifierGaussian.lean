import Foundation.IBMBoundaryVariance

/-! Joint Gaussian source law of the mollified scenery and spatial derivatives. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMJointMollifierGaussian
open InfiniteGaussian GaussianHilbertProcess FractionalSpectralKernel
open IBMFiniteScenerySmoothing IBMContinuousScenery IBMMollifier
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

def wholeLineDirection (ρ : ℝ → ℝ) (x : ℝ) : SpectralSpace :=
  ∫ r, ρ (x - r) • direction r

theorem wholeLineScenery_eq_sourceEmbedding (ρ : ℝ → ℝ) (x : ℝ) :
    wholeLineScenery ρ x =
      isonormalEmbedding SpectralSpace (wholeLineDirection ρ x) := by
  rw [wholeLineScenery_eq_integral]
  unfold wholeLineDirection
  rw [← (isonormalEmbedding SpectralSpace).integral_comp_comm]
  congr 1
  funext r
  simp only [sourceScenery, map_smul]

def derivativeKernel (n : ℕ) : Fin 3 → ℝ → ℝ :=
  fun i => if i = 0 then kernel n else if i = 1 then deriv (kernel n)
    else deriv (deriv (kernel n))

def gaussianTriple (n : ℕ) (x : ℝ) (i : Fin 3) : SampleSpace → ℝ :=
  isonormal SpectralSpace (wholeLineDirection (derivativeKernel n i) x)

theorem gaussianTriple_jointGaussian (n : ℕ) (x : ℝ) :
    IsGaussianProcess (gaussianTriple n x) gaussianProduct :=
  isonormal_isGaussianProcess.comp_right
    (fun i : Fin 3 => wholeLineDirection (derivativeKernel n i) x)

theorem gaussianTriple_covariance (n : ℕ) (x : ℝ) (i j : Fin 3) :
    cov[gaussianTriple n x i, gaussianTriple n x j; gaussianProduct] =
      inner ℝ (wholeLineDirection (derivativeKernel n i) x)
        (wholeLineDirection (derivativeKernel n j) x) := by
  exact isonormal_covariance _ _

theorem gaussianTriple_zero_eq (n : ℕ) (x : ℝ) :
    wholeLineScenery (kernel n) x =
      isonormalEmbedding SpectralSpace (wholeLineDirection (derivativeKernel n 0) x) := by
  simpa [derivativeKernel] using wholeLineScenery_eq_sourceEmbedding (kernel n) x

theorem gaussianTriple_one_eq (n : ℕ) (x : ℝ) :
    wholeLineScenery (deriv (kernel n)) x =
      isonormalEmbedding SpectralSpace (wholeLineDirection (derivativeKernel n 1) x) := by
  simpa [derivativeKernel] using
    wholeLineScenery_eq_sourceEmbedding (deriv (kernel n)) x

theorem gaussianTriple_two_eq (n : ℕ) (x : ℝ) :
    wholeLineScenery (deriv (deriv (kernel n))) x =
      isonormalEmbedding SpectralSpace (wholeLineDirection (derivativeKernel n 2) x) := by
  simpa [derivativeKernel] using
    wholeLineScenery_eq_sourceEmbedding (deriv (deriv (kernel n))) x

theorem gaussianTriple_interior_covariance_half (n : ℕ) (x : ℝ)
    (hbulk : (bump n).rOut < x) :
    cov[gaussianTriple n x 0, gaussianTriple n x 1; gaussianProduct] = 1 / 2 := by
  rw [gaussianTriple_covariance]
  have h := IBMOffsetTranslation.concrete_interior_cross_covariance n x hbulk
  rw [gaussianTriple_zero_eq, gaussianTriple_one_eq,
    LinearIsometry.inner_map_map] at h
  exact h

theorem gaussianTriple_interior_covariance_cancellation (n : ℕ) (x : ℝ)
    (hbulk : (bump n).rOut < x) :
    cov[gaussianTriple n x 1, gaussianTriple n x 1; gaussianProduct] +
      cov[gaussianTriple n x 0, gaussianTriple n x 2; gaussianProduct] = 0 := by
  rw [gaussianTriple_covariance, gaussianTriple_covariance]
  have h := IBMOffsetTranslation.concrete_interior_covariance_cancellation n x hbulk
  rw [gaussianTriple_zero_eq, gaussianTriple_one_eq, gaussianTriple_two_eq,
    LinearIsometry.norm_map, LinearIsometry.inner_map_map] at h
  rwa [real_inner_self_eq_norm_sq]

end OperatorDerivativeRewrite.Foundation.IBMJointMollifierGaussian
