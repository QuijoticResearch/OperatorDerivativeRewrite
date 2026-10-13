import Foundation.IBMFiniteScenerySmoothing
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Source-first Bochner integration of the verified Gaussian scenery.
No sample-path modification is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
open InfiniteGaussian FractionalSpectralKernel FractionalSpectralGeometry
open GaussianHilbertProcess IBMSourceLaws IBMFiniteScenerySmoothing
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

/-- The actual Gaussian L² coordinate of the two-sided scenery. -/
def sourceScenery (r : ℝ) : GaussianL2 :=
  isonormalEmbedding SpectralSpace (direction r)

theorem direction_continuous : Continuous direction := by
  unfold direction
  exact normalized_continuous (1/2) (by norm_num) (by norm_num)

theorem sourceScenery_continuous : Continuous sourceScenery := by
  exact (isonormalEmbedding SpectralSpace).continuous.comp direction_continuous

/-- The source field is strongly measurable as an L²-valued map. -/
theorem sourceScenery_stronglyMeasurable : StronglyMeasurable sourceScenery :=
  sourceScenery_continuous.stronglyMeasurable

theorem sourceScenery_integrableOn (a b : ℝ) :
    IntegrableOn sourceScenery (Set.Icc a b) volume :=
  sourceScenery_continuous.integrableOn_Icc

/-- Exact Brownian spatial increment energy in the genuine Gaussian L² space. -/
theorem sourceScenery_increment_sq (s r : ℝ) :
    ‖sourceScenery r - sourceScenery s‖ ^ 2 = |r - s| := by
  rw [sourceScenery, sourceScenery, ← (isonormalEmbedding SpectralSpace).map_sub,
    (isonormalEmbedding SpectralSpace).norm_map]
  exact direction_increment_sq s r

/-- Compact-interval spatial kernel applied to the Brownian Hilbert directions. -/
def kernelDirection (a b x : ℝ) (ρ : ℝ → ℝ) : SpectralSpace :=
  ∫ r in Set.Icc a b, ρ (x - r) • direction r

/-- The corresponding genuine Gaussian L² Bochner convolution. -/
def kernelScenery (a b x : ℝ) (ρ : ℝ → ℝ) : GaussianL2 :=
  ∫ r in Set.Icc a b, ρ (x - r) • sourceScenery r

theorem weightedDirection_continuous (x : ℝ) {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    Continuous (fun r : ℝ => ρ (x - r) • direction r) := by
  exact (hρ.comp (continuous_const.sub continuous_id)).smul direction_continuous

theorem weightedScenery_continuous (x : ℝ) {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    Continuous (fun r : ℝ => ρ (x - r) • sourceScenery r) := by
  exact (hρ.comp (continuous_const.sub continuous_id)).smul sourceScenery_continuous

theorem weightedDirection_integrableOn (a b x : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) :
    IntegrableOn (fun r : ℝ => ρ (x - r) • direction r) (Set.Icc a b) volume :=
  (weightedDirection_continuous x hρ).integrableOn_Icc

theorem weightedScenery_integrableOn (a b x : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) :
    IntegrableOn (fun r : ℝ => ρ (x - r) • sourceScenery r) (Set.Icc a b) volume :=
  (weightedScenery_continuous x hρ).integrableOn_Icc

/-- Bochner convolution commutes with the verified isonormal embedding. -/
theorem kernelScenery_eq_embedding (a b x : ℝ) (ρ : ℝ → ℝ) :
    kernelScenery a b x ρ =
      isonormalEmbedding SpectralSpace (kernelDirection a b x ρ) := by
  unfold kernelScenery kernelDirection
  have h := (isonormalEmbedding SpectralSpace).integral_comp_comm
    (μ := volume.restrict (Set.Icc a b))
    (fun r : ℝ => ρ (x - r) • direction r)
  simpa only [sourceScenery, map_smul] using h

theorem kernelScenery_norm (a b x : ℝ) (ρ : ℝ → ℝ) :
    ‖kernelScenery a b x ρ‖ = ‖kernelDirection a b x ρ‖ := by
  rw [kernelScenery_eq_embedding]
  exact (isonormalEmbedding SpectralSpace).norm_map _

/-- Every continuous compact-interval kernel has the expected covariance
against one verified Brownian scenery coordinate. -/
theorem direction_inner_kernel (a b x y : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) :
    inner ℝ (direction y) (kernelDirection a b x ρ) =
      ∫ r in Set.Icc a b, ρ (x - r) * covariance (1/2) y r := by
  rw [kernelDirection, ← integral_inner (weightedDirection_integrableOn a b x hρ)]
  congr 1
  funext r
  simp only [real_inner_smul_right]
  rw [show inner ℝ (direction y) (direction r) = covariance (1/2) y r by
    simp only [direction, normalized_inner]]

/-- The actual Gaussian source cross moment of the continuous Bochner
convolution is the integral of the Brownian covariance kernel. -/
theorem kernelScenery_cross_moment_source (a b x y : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) :
    (∫ ω, isonormal SpectralSpace (kernelDirection a b x ρ) ω *
      sceneryBase y ω ∂gaussianProduct) =
      ∫ r in Set.Icc a b, ρ (x - r) * covariance (1/2) y r := by
  change (∫ ω, isonormal SpectralSpace (kernelDirection a b x ρ) ω *
    isonormal SpectralSpace (direction y) ω ∂gaussianProduct) = _
  rw [isonormal_product_integral]
  rw [real_inner_comm]
  exact direction_inner_kernel a b x y hρ

end OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
