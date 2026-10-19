import Foundation.IBMPhysicalNoiseRealization
import Foundation.IBMUnmollifiedSourceDerivative

/-! Physical kernels for the actual smooth scenery convolutions and their
closed Gaussian source derivative. No negative-Sobolev convergence of the
full random correction is inferred from this coordinate realization. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalNoiseCalculus
open InfiniteGaussian GaussianTimeHilbert IBMPhysicalNoiseVectors
open IBMPhysicalNoiseRealization IBMFullSchwartzTerminal IBMQuarticPrimitiveLimit
open IBMContinuousScenery GaussianPastFirstChaos GaussianBrownianSobolevField

theorem physical_adjoint_leftInverse (f : TimeHilbert) :
    physicalToCoefficient.toContinuousLinearMap.adjoint (physicalToCoefficient f) = f := by
  exact congrArg (fun L : TimeHilbert →L[ℝ] TimeHilbert => L f)
    physicalToCoefficient.adjoint_comp_self

theorem physical_adjoint_base (r : ℝ) :
    physicalToCoefficient.toContinuousLinearMap.adjoint (baseCoefficient r) = vector r := by
  rw [← physicalToCoefficient_vector, physical_adjoint_leftInverse]

theorem vector_continuous : Continuous vector := by
  have hc : Continuous baseCoefficient :=
    firstChaosEmbedding.toContinuousLinearMap.adjoint.continuous.comp sourceScenery_continuous
  have he : vector = fun r => physicalToCoefficient.toContinuousLinearMap.adjoint (baseCoefficient r) :=
    funext fun r => (physical_adjoint_base r).symm
  rw [he]
  exact physicalToCoefficient.toContinuousLinearMap.adjoint.continuous.comp hc

/-- This graph is the already verified closed Gaussian derivative graph. -/
theorem physicalNoise_closedDerivative_graph (f : TimeHilbert) :
    (physicalNoise f,Lp.const 2 gaussianProduct (physicalToCoefficient f)) ∈
      closedCylindricalDerivative.graph := by
  have hg := projection_closedDerivative_graph (physicalNoise f)
  have he : projection (physicalNoise f) = physicalNoise f := by
    change firstChaosEmbedding (firstChaosEmbedding.toContinuousLinearMap.adjoint
      (firstChaosEmbedding (physicalToCoefficient f))) = _
    rw [IBMQuarticSecondPrimitive.adjoint_embedding]
    rfl
  rw [he] at hg
  change (physicalNoise f,firstChaosGradient (firstChaosEmbedding (physicalToCoefficient f))) ∈ _ at hg
  rwa [firstChaosGradient_apply] at hg

/-- Physical coordinate pullback of a Gaussian gradient field. No closedness
claim for an unrestricted postcomposed derivative is made here. -/
def gradientPullback : GaussianVectorL2 →L[ℝ] Lp TimeHilbert 2 gaussianProduct :=
  physicalToCoefficient.toContinuousLinearMap.adjoint.compLpL 2 gaussianProduct

theorem gradientPullback_const (f : TimeHilbert) :
    gradientPullback (Lp.const 2 gaussianProduct (physicalToCoefficient f)) =
      Lp.const 2 gaussianProduct f := by
  apply Lp.ext
  filter_upwards [physicalToCoefficient.toContinuousLinearMap.adjoint.coeFn_compLpL
    (Lp.const 2 gaussianProduct (physicalToCoefficient f)),
    Lp.coeFn_const (p := 2) (μ := gaussianProduct) (c := physicalToCoefficient f),
    Lp.coeFn_const (p := 2) (μ := gaussianProduct) (c := f)] with ω hp hc hf
  change gradientPullback (Lp.const 2 gaussianProduct (physicalToCoefficient f)) ω = _ at hp
  rw [hp, hc, hf]
  exact physical_adjoint_leftInverse f

def convolutionKernel (ρ : ℝ → ℝ) (x : ℝ) : TimeHilbert := ∫ r, ρ (x-r) • vector r

theorem convolutionKernel_integrable {ρ : ℝ → ℝ} (hc : Continuous ρ)
    (hs : HasCompactSupport ρ) (x : ℝ) : Integrable (fun r => ρ (x-r) • vector r) volume := by
  have hcs : HasCompactSupport (fun r => ρ (x-r)) := hs.comp_homeomorph (Homeomorph.subLeft x)
  exact ((hc.comp (continuous_const.sub continuous_id)).smul vector_continuous).integrable_of_hasCompactSupport
    hcs.smul_right

/-- Actual source equality, not merely equality in distribution. -/
theorem convolutionKernel_realizes {ρ : ℝ → ℝ} (hc : Continuous ρ)
    (hs : HasCompactSupport ρ) (x : ℝ) :
    physicalNoise (convolutionKernel ρ x) = wholeLineScenery ρ x := by
  have he : physicalNoise (convolutionKernel ρ x) =
      ∫ r, physicalNoise (ρ (x-r) • vector r) :=
    (physicalNoise.toContinuousLinearMap.integral_comp_comm (convolutionKernel_integrable hc hs x)).symm
  rw [wholeLineScenery_eq_integral]
  apply he.trans
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by simp only [map_smul, physicalNoise_vector]

theorem convolutionKernel_coefficient {ρ : ℝ → ℝ} (hc : Continuous ρ)
    (hs : HasCompactSupport ρ) (x : ℝ) :
    physicalToCoefficient (convolutionKernel ρ x) =
      firstChaosEmbedding.toContinuousLinearMap.adjoint (wholeLineScenery ρ x) := by
  rw [← convolutionKernel_realizes hc hs x]
  exact (IBMQuarticSecondPrimitive.adjoint_embedding _).symm

theorem convolution_closedDerivative_graph {ρ : ℝ → ℝ} (hc : Continuous ρ)
    (hs : HasCompactSupport ρ) (x : ℝ) :
    (wholeLineScenery ρ x,Lp.const 2 gaussianProduct
      (physicalToCoefficient (convolutionKernel ρ x))) ∈ closedCylindricalDerivative.graph := by
  rw [← convolutionKernel_realizes hc hs x]
  exact physicalNoise_closedDerivative_graph _

/-- Pulling the actual closed source gradient back yields the physical
Lebesgue-L2 convolution kernel as a deterministic random field. -/
theorem convolution_gradient_pullback {ρ : ℝ → ℝ} (hc : Continuous ρ)
    (hs : HasCompactSupport ρ) (x : ℝ) :
    gradientPullback (firstChaosGradient (wholeLineScenery ρ x)) =
      Lp.const 2 gaussianProduct (convolutionKernel ρ x) := by
  rw [← convolutionKernel_realizes hc hs x]
  change gradientPullback (firstChaosGradient
    (firstChaosEmbedding (physicalToCoefficient (convolutionKernel ρ x)))) = _
  rw [firstChaosGradient_apply, gradientPullback_const]

theorem derivativeKernel_continuous (n : ℕ) (i : Fin 3) :
    Continuous (IBMJointMollifierGaussian.derivativeKernel n i) := by
  have h0 : ContDiff ℝ 3 (IBMMollifier.kernel n) := (IBMMollifier.kernel_smooth n).of_le (by norm_num)
  have h1 : ContDiff ℝ 2 (deriv (IBMMollifier.kernel n)) := h0.deriv' (n := 2)
  have h2 : ContDiff ℝ 1 (deriv (deriv (IBMMollifier.kernel n))) := h1.deriv' (n := 1)
  fin_cases i
  · simpa [IBMJointMollifierGaussian.derivativeKernel] using h0.continuous
  · simpa [IBMJointMollifierGaussian.derivativeKernel] using h1.continuous
  · simpa [IBMJointMollifierGaussian.derivativeKernel] using h2.continuous

theorem derivativeKernel_compact (n : ℕ) (i : Fin 3) :
    HasCompactSupport (IBMJointMollifierGaussian.derivativeKernel n i) := by
  fin_cases i
  · simpa [IBMJointMollifierGaussian.derivativeKernel] using IBMMollifier.kernel_compactSupport n
  · simpa [IBMJointMollifierGaussian.derivativeKernel] using (IBMMollifier.kernel_compactSupport n).deriv
  · simpa [IBMJointMollifierGaussian.derivativeKernel] using
      (IBMMollifier.kernel_compactSupport n).deriv.deriv

theorem triple_coefficient_physical (n : ℕ) (r : ℝ) (i : Fin 3) :
    physicalToCoefficient (convolutionKernel (IBMJointMollifierGaussian.derivativeKernel n i) r) =
      IBMGaussianSteinMoments.tripleCoefficient n r i := by
  rw [convolutionKernel_coefficient (derivativeKernel_continuous n i) (derivativeKernel_compact n i) r]
  exact IBMQuarticSecondPrimitive.adjoint_scenery n r i

/-- Physical-space strong L2 convergence of the actual zeroth mollifier
kernel to the oriented Brownian indicator, on both sides of the origin. -/
theorem mollifier_kernel_tendsto (r : ℝ) :
    Tendsto (fun n => convolutionKernel (IBMMollifier.kernel n) r) atTop (𝓝 (vector r)) := by
  have he := physicalToCoefficient.toContinuousLinearMap.adjoint.continuous.tendsto
    (baseCoefficient r) |>.comp (coefficient_tendsto r)
  have hn (n : ℕ) : physicalToCoefficient.toContinuousLinearMap.adjoint
      (IBMGaussianSteinMoments.tripleCoefficient n r 0) = convolutionKernel (IBMMollifier.kernel n) r := by
    rw [← triple_coefficient_physical, physical_adjoint_leftInverse]
    rfl
  simpa only [Function.comp_def, hn, physical_adjoint_base] using he

end OperatorDerivativeRewrite.Foundation.IBMPhysicalNoiseCalculus
