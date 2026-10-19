import Foundation.IBMSchwartzPhysicalPrimitive
import Foundation.BochnerL2Approximation

/-! Strong clock-L2 endpoints of the first-source spatial primitive. The
unprojected endpoints are actual nonlinear IBM observables. No convergence
of their spatial second derivatives or whole correction is inferred. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalPrimitiveClock
open InfiniteGaussian GaussianTimeHilbert IBMCorrectionStein IBMSchwartzSourceDerivative
open IBMFullSchwartzTerminal IBMConstructedSources IBMPhysicalNoiseClock
open IBMPhysicalNoiseRealization IBMSchwartzPhysicalPrimitive

theorem endpoint_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    MemLp (fun ω => spatial g a n |clockPath ω T|) 2 gaussianProduct := by
  apply MemLp.of_bound
    ((spatial_continuous g a n).stronglyMeasurable.comp_measurable
      (IBMQuarticClockTerminal.clockPosition_measurable T)).aestronglyMeasurable
    (SchwartzMap.seminorm ℝ 0 0 (jet g 0))
  exact Eventually.of_forall fun ω => observable_bound g a 0 _

theorem endpointLimit_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    MemLp (fun ω => spatialLimit g a |clockPath ω T|) 2 gaussianProduct := by
  apply MemLp.of_bound
    ((spatialLimit_continuous g a).stronglyMeasurable.comp_measurable
      (IBMQuarticClockTerminal.clockPosition_measurable T)).aestronglyMeasurable
    (SchwartzMap.seminorm ℝ 0 0 (jet g 0))
  exact Eventually.of_forall fun ω => observable_bound g a 0 _

def endpoint (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Lp GaussianL2 2 gaussianProduct := (endpoint_memLp g a n T).toLp _

def endpointLimit (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Lp GaussianL2 2 gaussianProduct := (endpointLimit_memLp g a T).toLp _

theorem endpoint_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    endpoint g a n T =ᵐ[gaussianProduct] fun ω => spatial g a n |clockPath ω T| :=
  MemLp.coeFn_toLp _

theorem endpointLimit_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    endpointLimit g a T =ᵐ[gaussianProduct] fun ω => spatialLimit g a |clockPath ω T| :=
  MemLp.coeFn_toLp _

/-- The limit retains all source chaos degrees, on the actual independent
clock, with sections given by the already constructed continuous IBM. -/
theorem endpointLimit_actual_sections (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ωY ∂gaussianProduct, endpointLimit g a T ωY =ᵐ[gaussianProduct]
      fun ωX => g (a+ibmValue T (ωX,ωY)) := by
  filter_upwards [endpointLimit_ae g a T] with ωY he
  rw [he]
  exact actual_section g a T ωY

theorem endpoint_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => endpoint g a n T) atTop (𝓝 (endpointLimit g a T)) := by
  let C := SchwartzMap.seminorm ℝ 0 0 (jet g 0)
  have hC : 0 ≤ C := by positivity
  have hb : ∀ᵐ ω ∂gaussianProduct, ‖(C • gaussianOne : GaussianL2) ω‖ = C := by
    filter_upwards [Lp.coeFn_smul C gaussianOne, gaussianOne_coeFn] with ω hs ho
    simp only [hs, Pi.smul_apply, smul_eq_mul, ho, mul_one, Real.norm_eq_abs, abs_of_nonneg hC]
  apply BochnerL2Approximation.tendsto_of_dominated _ _ (C • gaussianOne)
  · intro n
    filter_upwards [endpoint_ae g a n T, hb] with ω he hω
    rw [he, hω]
    exact observable_bound g a 0 _
  · filter_upwards [endpointLimit_ae g a T, hb] with ω he hω
    rw [he, hω]
    exact observable_bound g a 0 _
  · filter_upwards [ae_all_iff.mpr (fun n => endpoint_ae g a n T),
      endpointLimit_ae g a T] with ω hn hlim
    simp only [hn, hlim]
    exact spatial_tendsto g a _

def primitiveClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Lp TimeHilbert 2 gaussianProduct := kernelPullback.compLpL 2 gaussianProduct (endpoint g a n T)

def primitiveLimitClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Lp TimeHilbert 2 gaussianProduct := kernelPullback.compLpL 2 gaussianProduct (endpointLimit g a T)

theorem primitiveClass_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    primitiveClass g a n T =ᵐ[gaussianProduct] fun ω => primitive g a n |clockPath ω T| := by
  filter_upwards [kernelPullback.coeFn_compLpL (endpoint g a n T), endpoint_ae g a n T]
    with ω hp he
  change primitiveClass g a n T ω = kernelPullback (endpoint g a n T ω) at hp
  rw [hp, he]
  rfl

theorem primitiveLimitClass_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    primitiveLimitClass g a T =ᵐ[gaussianProduct] fun ω => primitiveLimit g a |clockPath ω T| := by
  filter_upwards [kernelPullback.coeFn_compLpL (endpointLimit g a T), endpointLimit_ae g a T]
    with ω hp he
  change primitiveLimitClass g a T ω = kernelPullback (endpointLimit g a T ω) at hp
  rw [hp, he]
  rfl

theorem primitiveClass_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => primitiveClass g a n T) atTop (𝓝 (primitiveLimitClass g a T)) :=
  (kernelPullback.compLpL 2 gaussianProduct).continuous.tendsto _ |>.comp (endpoint_tendsto g a T)

theorem primitiveClass_realizes_projection (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    physicalNoise.toContinuousLinearMap.compLpL 2 gaussianProduct (primitiveClass g a n T) =
      GaussianPastFirstChaos.projection.compLpL 2 gaussianProduct (endpoint g a n T) := by
  apply Lp.ext
  filter_upwards [physicalNoise.toContinuousLinearMap.coeFn_compLpL (primitiveClass g a n T),
    GaussianPastFirstChaos.projection.coeFn_compLpL (endpoint g a n T),
    primitiveClass_ae g a n T, endpoint_ae g a n T] with ω hW hP hp he
  rw [hW, hP, hp, he]
  exact primitive_realizes_projection g a n _

theorem primitiveLimitClass_realizes_projection (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    physicalNoise.toContinuousLinearMap.compLpL 2 gaussianProduct (primitiveLimitClass g a T) =
      GaussianPastFirstChaos.projection.compLpL 2 gaussianProduct (endpointLimit g a T) := by
  apply Lp.ext
  filter_upwards [physicalNoise.toContinuousLinearMap.coeFn_compLpL (primitiveLimitClass g a T),
    GaussianPastFirstChaos.projection.coeFn_compLpL (endpointLimit g a T),
    primitiveLimitClass_ae g a T, endpointLimit_ae g a T] with ω hW hP hp he
  rw [hW, hP, hp, he]
  exact primitiveLimit_realizes_projection g a _

end OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalPrimitiveClock
