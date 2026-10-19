import Foundation.IBMPhysicalNoiseCalculus
import Foundation.IBMNegativeSobolevRandom

/-! Actual physical-space kernels at the constructed Brownian clock, and
strong Bochner-L2 convergence of their physical distributional derivatives.
These are not yet the manuscript's entire correction kernels. -/
noncomputable section
open MeasureTheory Filter TemperedDistribution
open scoped Topology NNReal BesselPotentialSpace SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalNoiseClock
open InfiniteGaussian GaussianTimeHilbert IBMPhysicalNoiseVectors
open IBMPhysicalNoiseRealization IBMPhysicalNoiseCalculus IBMRandomTimeHilbert

def kernelPullback : GaussianL2 →L[ℝ] TimeHilbert :=
  physicalToCoefficient.toContinuousLinearMap.adjoint.comp firstChaosEmbedding.toContinuousLinearMap.adjoint

theorem kernelPullback_noise (f : TimeHilbert) : kernelPullback (physicalNoise f) = f := by
  change physicalToCoefficient.toContinuousLinearMap.adjoint
    (firstChaosEmbedding.toContinuousLinearMap.adjoint (firstChaosEmbedding (physicalToCoefficient f))) = _
  rw [IBMQuarticSecondPrimitive.adjoint_embedding, physical_adjoint_leftInverse]

theorem kernelPullback_source (r : ℝ) : kernelPullback (IBMContinuousScenery.sourceScenery r) = vector r := by
  rw [← physicalNoise_vector, kernelPullback_noise]

theorem kernelPullback_convolution {ρ : ℝ → ℝ} (hc : Continuous ρ)
    (hs : HasCompactSupport ρ) (r : ℝ) :
    kernelPullback (IBMContinuousScenery.wholeLineScenery ρ r) = convolutionKernel ρ r := by
  rw [← convolutionKernel_realizes hc hs r, kernelPullback_noise]

def mollifiedKernel (n : ℕ) (t : ℝ≥0) : Lp TimeHilbert 2 gaussianProduct :=
  kernelPullback.compLpL 2 gaussianProduct (randomMollifiedL2 n t)

def sourceKernel (t : ℝ≥0) : Lp TimeHilbert 2 gaussianProduct :=
  kernelPullback.compLpL 2 gaussianProduct (randomSourceL2 t)

theorem mollifiedKernel_ae (n : ℕ) (t : ℝ≥0) :
    mollifiedKernel n t =ᵐ[gaussianProduct] fun ω =>
      convolutionKernel (IBMMollifier.kernel n) |IBMConstructedSources.clockPath ω t| := by
  filter_upwards [kernelPullback.coeFn_compLpL (randomMollifiedL2 n t),
    (randomMollifiedClass_memLp n t).coeFn_toLp,
    IBMConstructedSources.clockPath_coordinate_ae t] with ω hp hm hc
  change mollifiedKernel n t ω = kernelPullback (randomMollifiedL2 n t ω) at hp
  change randomMollifiedL2 n t ω = randomMollifiedClass n t ω at hm
  rw [hp, hm]
  change kernelPullback (IBMContinuousScenery.wholeLineScenery (IBMMollifier.kernel n)
    |GaussianTimeProcess.process t ω|) = _
  rw [kernelPullback_convolution (IBMMollifier.kernel_smooth n).continuous
    (IBMMollifier.kernel_compactSupport n), hc]

theorem sourceKernel_ae (t : ℝ≥0) : sourceKernel t =ᵐ[gaussianProduct]
    fun ω => vector |IBMConstructedSources.clockPath ω t| := by
  filter_upwards [kernelPullback.coeFn_compLpL (randomSourceL2 t),
    (randomSourceClass_memLp t).coeFn_toLp,
    IBMConstructedSources.clockPath_coordinate_ae t] with ω hp hm hc
  change sourceKernel t ω = kernelPullback (randomSourceL2 t ω) at hp
  change randomSourceL2 t ω = randomSourceClass t ω at hm
  rw [hp, hm]
  change kernelPullback (IBMContinuousScenery.sourceScenery |GaussianTimeProcess.process t ω|) = _
  rw [kernelPullback_source, hc]

/-- The actual independent-clock source sections are recovered by applying
the physical noise, with the already constructed continuous IBM paths. -/
theorem sourceKernel_actual_realization (t : ℝ≥0) : ∀ᵐ ωY ∂gaussianProduct,
    physicalNoise (sourceKernel t ωY) =ᵐ[gaussianProduct]
      fun ωX => IBMConstructedSources.ibmValue t (ωX,ωY) := by
  filter_upwards [sourceKernel_ae t] with ωY hk
  rw [hk, physicalNoise_vector]
  exact (IBMConstructedSources.sceneryPath_coordinate_ae
    |IBMConstructedSources.clockPath ωY t|).symm

theorem mollifiedKernel_tendsto (t : ℝ≥0) :
    Tendsto (fun n => mollifiedKernel n t) atTop (𝓝 (sourceKernel t)) :=
  (kernelPullback.compLpL 2 gaussianProduct).continuous.tendsto _ |>.comp (randomMollifiedL2_tendsto t)

/-- Complexification uses the usual scalar embedding; the physical spatial
variable and the Lebesgue measure are unchanged. -/
def complexify : TimeHilbert →L[ℝ] Lp ℂ 2 (volume : Measure ℝ) :=
  Complex.ofRealCLM.compLpL 2 volume

def physicalDerivative : TimeHilbert →L[ℝ] H^{(-1 : ℝ)}(ℝ) :=
  (IBMNegativeSobolevBounded.l2DerivativeCLM.restrictScalars ℝ).comp complexify

theorem physicalDerivative_toDistr (f : TimeHilbert) :
    (physicalDerivative f).toDistr =
      LineDeriv.lineDerivOp (1 : ℝ) ((complexify f : Lp ℂ 2 volume) : 𝓢'(ℝ,ℂ)) := by
  exact IBMNegativeSobolev.l2Derivative_toDistr _

def mollifiedDerivative (n : ℕ) (t : ℝ≥0) : Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct :=
  physicalDerivative.compLpL 2 gaussianProduct (mollifiedKernel n t)

def sourceDerivative (t : ℝ≥0) : Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct :=
  physicalDerivative.compLpL 2 gaussianProduct (sourceKernel t)

theorem mollifiedDerivative_ae (n : ℕ) (t : ℝ≥0) : mollifiedDerivative n t =ᵐ[gaussianProduct]
    fun ω => physicalDerivative (convolutionKernel (IBMMollifier.kernel n)
      |IBMConstructedSources.clockPath ω t|) := by
  filter_upwards [physicalDerivative.coeFn_compLpL (mollifiedKernel n t), mollifiedKernel_ae n t] with ω hd hk
  change mollifiedDerivative n t ω = physicalDerivative (mollifiedKernel n t ω) at hd
  rw [hd, hk]

theorem sourceDerivative_ae (t : ℝ≥0) : sourceDerivative t =ᵐ[gaussianProduct]
    fun ω => physicalDerivative (vector |IBMConstructedSources.clockPath ω t|) := by
  filter_upwards [physicalDerivative.coeFn_compLpL (sourceKernel t), sourceKernel_ae t] with ω hd hk
  change sourceDerivative t ω = physicalDerivative (sourceKernel t ω) at hd
  rw [hd, hk]

/-- Strong L2(clock;H^-1(physical space)), rather than an unspecified
sequence topology or a coefficient-space negative norm. -/
theorem mollifiedDerivative_tendsto (t : ℝ≥0) :
    Tendsto (fun n => mollifiedDerivative n t) atTop (𝓝 (sourceDerivative t)) :=
  (physicalDerivative.compLpL 2 gaussianProduct).continuous.tendsto _ |>.comp (mollifiedKernel_tendsto t)

end OperatorDerivativeRewrite.Foundation.IBMPhysicalNoiseClock
