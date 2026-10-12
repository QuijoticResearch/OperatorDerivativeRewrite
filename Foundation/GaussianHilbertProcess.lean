import Foundation.SeparableHilbertEmbedding
import Foundation.InfiniteGaussianIsonormal
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# A concrete isonormal process over a separable real Hilbert space

The coordinate embedding is constructed from a Hilbert basis, rather than an
assumed realization. Its composition with the verified first-chaos isometry
gives actual Gaussian random variables on the existing countable product.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OperatorDerivativeRewrite.Foundation.GaussianHilbertProcess

open InfiniteGaussian SeparableHilbertEmbedding

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SecondCountableTopology H]

/-- The actual isonormal L² isometry, with a constructed Hilbert coordinate map. -/
def isonormalEmbedding : H →ₗᵢ[ℝ] GaussianL2 :=
  firstChaosEmbedding.comp (hilbertEmbedding H)

/-- Actual measurable representatives of the constructed Gaussian L² classes. -/
def isonormal (h : H) : SampleSpace → ℝ := isonormalEmbedding H h

variable {H}

theorem isonormalEmbedding_add (h k : H) :
    isonormalEmbedding H (h + k) = isonormalEmbedding H h + isonormalEmbedding H k :=
  (isonormalEmbedding H).map_add h k

theorem isonormalEmbedding_smul (a : ℝ) (h : H) :
    isonormalEmbedding H (a • h) = a • isonormalEmbedding H h :=
  (isonormalEmbedding H).map_smul a h

theorem isonormalEmbedding_inner (h k : H) :
    inner ℝ (isonormalEmbedding H h) (isonormalEmbedding H k) = inner ℝ h k :=
  (isonormalEmbedding H).inner_map_map h k

theorem isonormal_measurable (h : H) : Measurable (isonormal H h) :=
  (Lp.stronglyMeasurable (isonormalEmbedding H h)).measurable

theorem isonormal_hasGaussianLaw (h : H) :
    HasGaussianLaw (isonormal H h) gaussianProduct :=
  firstChaos_hasGaussianLaw (hilbertEmbedding H h)

/-- The variance parameter is exactly the original Hilbert norm, including zero. -/
theorem isonormal_law (h : H) :
    gaussianProduct.map (isonormal H h) =
      gaussianReal 0 (NNReal.mk (‖h‖ ^ 2) (sq_nonneg _)) := by
  change gaussianProduct.map (firstChaosEmbedding (hilbertEmbedding H h)) = _
  rw [firstChaos_law, (hilbertEmbedding H).norm_map]

theorem isonormal_memLp (h : H) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (isonormal H h) p gaussianProduct :=
  (isonormal_hasGaussianLaw h).memLp hp

theorem isonormal_integral (h : H) :
    (∫ ω, isonormal H h ω ∂gaussianProduct) = 0 :=
  firstChaos_integral (hilbertEmbedding H h)

theorem isonormal_product_integrable (h k : H) :
    Integrable (fun ω => isonormal H h ω * isonormal H k ω) gaussianProduct := by
  exact ((isonormal_memLp h 2 (by simp)).fun_mul
    (isonormal_memLp k 2 (by simp)) : MemLp _ 1 gaussianProduct).integrable (by simp)

theorem isonormal_product_integral (h k : H) :
    (∫ ω, isonormal H h ω * isonormal H k ω ∂gaussianProduct) = inner ℝ h k := by
  change (∫ ω, firstChaosEmbedding (hilbertEmbedding H h) ω *
    firstChaosEmbedding (hilbertEmbedding H k) ω ∂gaussianProduct) = _
  rw [firstChaos_product_integral, (hilbertEmbedding H).inner_map_map]

theorem isonormal_covariance (h k : H) :
    cov[isonormal H h, isonormal H k; gaussianProduct] = inner ℝ h k := by
  change cov[firstChaosEmbedding (hilbertEmbedding H h),
    firstChaosEmbedding (hilbertEmbedding H k); gaussianProduct] = _
  rw [firstChaos_covariance, (hilbertEmbedding H).inner_map_map]

/-- Joint Gaussianity is proved for all finite families of Hilbert indices. -/
theorem isonormal_isGaussianProcess :
    IsGaussianProcess (isonormal H) gaussianProduct :=
  firstChaos_isGaussianProcess.comp_right (hilbertEmbedding H)

theorem isonormal_add_ae (h k : H) :
    isonormal H (h + k) =ᵐ[gaussianProduct]
      fun ω => isonormal H h ω + isonormal H k ω := by
  change (isonormalEmbedding H (h + k) : SampleSpace → ℝ) =ᵐ[_] _
  rw [isonormalEmbedding_add]
  exact Lp.coeFn_add _ _

theorem isonormal_sub_ae (h k : H) :
    isonormal H (h - k) =ᵐ[gaussianProduct]
      fun ω => isonormal H h ω - isonormal H k ω := by
  change (isonormalEmbedding H (h - k) : SampleSpace → ℝ) =ᵐ[_] _
  rw [(isonormalEmbedding H).map_sub]
  exact Lp.coeFn_sub _ _

theorem isonormal_smul_ae (a : ℝ) (h : H) :
    isonormal H (a • h) =ᵐ[gaussianProduct]
      fun ω => a * isonormal H h ω := by
  change (isonormalEmbedding H (a • h) : SampleSpace → ℝ) =ᵐ[_] _
  rw [isonormalEmbedding_smul]
  exact Lp.coeFn_smul a _

end OperatorDerivativeRewrite.Foundation.GaussianHilbertProcess
