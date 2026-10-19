import Foundation.IBMPhysicalDerivativeKernel
import Foundation.IBMSchwartzFirstCoefficient
import Foundation.IBMPhysicalNoiseClock
import Foundation.IBMSchwartzWholeSourceMean
import Foundation.IBMSchwartzBochnerDomain

/-! Explicit physical first-source kernels of the actual nonlinear Schwartz
curvature and whole correction, including the origin layer. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalFirstKernel
open InfiniteGaussian GaussianTimeHilbert IBMPhysicalNoiseRealization IBMPhysicalNoiseCalculus
open IBMPhysicalDerivativeKernel IBMPhysicalNoiseClock IBMCorrectionStein IBMShiftedJetMoments
open IBMGaussianSteinMoments IBMSchwartzFirstCoefficient
open IBMSchwartzTimeProjection (originClass wholeCorrection mollified_path_continuous)

abbrev physicalJet (n : ℕ) (r : ℝ) (i : Fin 3) : TimeHilbert :=
  convolutionKernel (IBMJointMollifierGaussian.derivativeKernel n i) r

theorem physicalJet_one_coeFn (n : ℕ) (r : ℝ) :
    physicalJet n r 1 =ᵐ[volume] fun w => IBMMollifier.kernel n (r-w) := by
  change convolutionKernel (deriv (IBMMollifier.kernel n)) r =ᵐ[volume] _
  rw [derivative_eq_translated ((IBMMollifier.kernel_smooth n).of_le (by norm_num))
    (IBMMollifier.kernel_compactSupport n)]
  exact translatedClass_coeFn _ _ _ _

theorem physicalJet_two_coeFn (n : ℕ) (r : ℝ) :
    physicalJet n r 2 =ᵐ[volume] fun w => deriv (IBMMollifier.kernel n) (r-w) := by
  have hf : ContDiff ℝ 2 (IBMMollifier.kernel n) := (IBMMollifier.kernel_smooth n).of_le (by norm_num)
  change convolutionKernel (deriv (deriv (IBMMollifier.kernel n))) r =ᵐ[volume] _
  rw [derivative_eq_translated (hf.deriv' (n := 1)) (IBMMollifier.kernel_compactSupport n).deriv]
  exact translatedClass_coeFn _ _ _ _

def curvatureKernel (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) : TimeHilbert :=
  let u := tripleCoefficient n r 0
  let v := tripleCoefficient n r 1
  let w := tripleCoefficient n r 2
  ((‖v‖^2+inner ℝ u w)*M g a u 3 0+(inner ℝ u v)^2*M g a u 5 0) • physicalJet n r 0+
    (2*inner ℝ u v*M g a u 3 0) • physicalJet n r 1+M g a u 1 0 • physicalJet n r 2

theorem curvatureKernel_embeds (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    physicalToCoefficient (curvatureKernel g a n r) =
      coefficient g a (tripleCoefficient n r 0) (tripleCoefficient n r 1) (tripleCoefficient n r 2) := by
  simp only [curvatureKernel, map_add, map_smul, physicalJet, triple_coefficient_physical, coefficient]

theorem curvatureKernel_eq_pullback (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    kernelPullback (IBMSchwartzSecondProjection.mollifiedClass g a n r) = curvatureKernel g a n r := by
  change physicalToCoefficient.toContinuousLinearMap.adjoint
    (firstChaosEmbedding.toContinuousLinearMap.adjoint
      (IBMSchwartzSecondProjection.correctionClass g a (tripleCoefficient n r 0)
        (tripleCoefficient n r 1) (tripleCoefficient n r 2))) = _
  rw [correction_adjoint, ← curvatureKernel_embeds, physical_adjoint_leftInverse]

def originKernel (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) : TimeHilbert :=
  M g a (tripleCoefficient n 0 0) 1 0 • physicalJet n 0 1

theorem originKernel_embeds (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    physicalToCoefficient (originKernel g a n) =
      firstChaosEmbedding.toContinuousLinearMap.adjoint (originClass g a n) := by
  change physicalToCoefficient (originKernel g a n) =
    firstChaosEmbedding.toContinuousLinearMap.adjoint
      (IBMSchwartzSecondProjection.weightedClass g a (tripleCoefficient n 0 0) 1
        (firstChaosEmbedding (tripleCoefficient n 0 1)))
  rw [weighted_linear_adjoint, IBMSchwartzWholeSourceMean.origin_covariance_zero, zero_mul,
    zero_smul, add_zero]
  simp only [originKernel, map_smul, physicalJet, triple_coefficient_physical]

theorem originKernel_eq_pullback (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    kernelPullback (originClass g a n) = originKernel g a n := by
  change physicalToCoefficient.toContinuousLinearMap.adjoint
    (firstChaosEmbedding.toContinuousLinearMap.adjoint (originClass g a n)) = _
  rw [← originKernel_embeds, physical_adjoint_leftInverse]

theorem curvatureKernel_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    Continuous (curvatureKernel g a n) := by
  have he : curvatureKernel g a n = fun r => kernelPullback
      (IBMSchwartzSecondProjection.mollifiedClass g a n r) :=
    funext fun r => (curvatureKernel_eq_pullback g a n r).symm
  rw [he]
  exact kernelPullback.continuous.comp (IBMSchwartzSourceContinuity.mollifiedClass_continuous g a n)

def wholeKernel (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0)
    (ω : SampleSpace) : TimeHilbert :=
  BrownianMassLimitIdentification.coordinateClass T ω • originKernel g a n+
    (1/2 : ℝ) • ∫ s in 0..(T : ℝ), curvatureKernel g a n
      |IBMConstructedSources.clockPath ω s.toNNReal|

/-- An exact first-source physical coefficient of the whole finite-mollifier
correction. This identifies the kernel but asserts no singular limit. -/
theorem wholeKernel_eq_pullback (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) :
    kernelPullback (wholeCorrection g a n T ω) = wholeKernel g a n T ω := by
  have he := kernelPullback.intervalIntegral_comp_comm (μ := volume)
    ((mollified_path_continuous g a n ω).intervalIntegrable 0 T)
  rw [wholeCorrection, map_add, map_smul, map_smul, originKernel_eq_pullback, ← he]
  simp only [curvatureKernel_eq_pullback, wholeKernel]

theorem wholeKernel_embeds (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) :
    physicalToCoefficient (wholeKernel g a n T ω) =
      firstChaosEmbedding.toContinuousLinearMap.adjoint (wholeCorrection g a n T ω) := by
  have hk : IntervalIntegrable (fun s : ℝ => curvatureKernel g a n
      |IBMConstructedSources.clockPath ω s.toNNReal|) volume 0 T :=
    ((curvatureKernel_continuous g a n).comp (continuous_abs.comp
      ((IBMConstructedSources.clockPath ω).continuous.comp continuous_real_toNNReal))).intervalIntegrable 0 T
  have hJ : physicalToCoefficient (∫ s in 0..(T : ℝ), curvatureKernel g a n
      |IBMConstructedSources.clockPath ω s.toNNReal|) =
      ∫ s in 0..(T : ℝ), physicalToCoefficient (curvatureKernel g a n
        |IBMConstructedSources.clockPath ω s.toNNReal|) :=
    (physicalToCoefficient.toContinuousLinearMap.intervalIntegral_comp_comm (μ := volume) hk).symm
  have hD := firstChaosEmbedding.toContinuousLinearMap.adjoint.intervalIntegral_comp_comm (μ := volume)
    ((mollified_path_continuous g a n ω).intervalIntegrable 0 T)
  have hc (r : ℝ) : physicalToCoefficient (curvatureKernel g a n r) =
      firstChaosEmbedding.toContinuousLinearMap.adjoint (IBMSchwartzSecondProjection.mollifiedClass g a n r) := by
    rw [curvatureKernel_embeds]
    exact (correction_adjoint g a _ _ _).symm
  simp only [wholeKernel, wholeCorrection, map_add, map_smul, originKernel_embeds]
  rw [hJ, ← hD]
  simp only [hc]

/-- Applying the actual physical noise to the identified whole kernel
recovers the ENTIRE first-source orthogonal projection at each fixed clock
representative. This is not a theorem about its singular limit. -/
theorem wholeKernel_realizes_projection (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) :
    physicalNoise (wholeKernel g a n T ω) = GaussianPastFirstChaos.projection (wholeCorrection g a n T ω) := by
  change firstChaosEmbedding (physicalToCoefficient (wholeKernel g a n T ω)) =
    firstChaosEmbedding (firstChaosEmbedding.toContinuousLinearMap.adjoint (wholeCorrection g a n T ω))
  rw [wholeKernel_embeds]

/-- Changing from coefficient coordinates to physical coordinates does
not improve the native Gaussian L2 topology. Any singular limit must use
an independently justified weaker physical topology or cancellation. -/
theorem wholeKernel_difference_norm (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (n m : ℕ) (T : ℝ≥0) (ω : SampleSpace) :
    ‖wholeKernel g a n T ω-wholeKernel g a m T ω‖ =
      ‖GaussianPastFirstChaos.projection (wholeCorrection g a n T ω)-
        GaussianPastFirstChaos.projection (wholeCorrection g a m T ω)‖ := by
  rw [← physicalNoise.norm_map, map_sub, wholeKernel_realizes_projection, wholeKernel_realizes_projection]

/-- The entire finite-mollifier first-source kernel is a genuine
L2(clock;L2(physical space)) class, retaining all clock chaos degrees. -/
def wholeKernelClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Lp TimeHilbert 2 gaussianProduct :=
  kernelPullback.compLpL 2 gaussianProduct (IBMSchwartzBochnerDomain.wholeClass g a n T)

theorem wholeKernelClass_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    wholeKernelClass g a n T =ᵐ[gaussianProduct] wholeKernel g a n T := by
  filter_upwards [kernelPullback.coeFn_compLpL (IBMSchwartzBochnerDomain.wholeClass g a n T),
    IBMSchwartzBochnerDomain.wholeClass_coeFn g a n T] with ω hk hc
  change wholeKernelClass g a n T ω = kernelPullback (IBMSchwartzBochnerDomain.wholeClass g a n T ω) at hk
  rw [hk, hc, wholeKernel_eq_pullback]

/-- Exact Bochner-class reconstruction by the physical noise, before any
clock projection or singular limit. -/
theorem wholeKernelClass_realizes_projection (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    physicalNoise.toContinuousLinearMap.compLpL 2 gaussianProduct (wholeKernelClass g a n T) =
      GaussianPastFirstChaos.projection.compLpL 2 gaussianProduct
        (IBMSchwartzBochnerDomain.wholeClass g a n T) := by
  apply Lp.ext
  filter_upwards [physicalNoise.toContinuousLinearMap.coeFn_compLpL (wholeKernelClass g a n T),
    GaussianPastFirstChaos.projection.coeFn_compLpL (IBMSchwartzBochnerDomain.wholeClass g a n T),
    wholeKernelClass_ae g a n T, IBMSchwartzBochnerDomain.wholeClass_coeFn g a n T] with ω hW hP hK hC
  rw [hW,hP,hK,hC]
  exact wholeKernel_realizes_projection g a n T ω

end OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalFirstKernel
