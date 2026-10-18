import Foundation.IBMSchwartzSourceDerivative
import Foundation.IBMSchwartzSourceZeroTails

/-! Whole source-space terminal observables and their strong mollifier limit.
These retain every scenery chaos sector. Identification with the entire
clock-averaged correction is a separate second-derivative/heat obligation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFullSchwartzTerminal
open InfiniteGaussian IBMCorrectionStein IBMSchwartzSourceDerivative
open IBMGaussianSteinMoments IBMQuarticPrimitiveLimit IBMConstructedSources
open IBMContinuousScenery GaussianNumberSectors
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

def spatial (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) : GaussianL2 :=
  observable g a 0 (tripleCoefficient n r 0)

def spatialLimit (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) : GaussianL2 :=
  observable g a 0 (baseCoefficient r)

theorem spatial_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (spatial g a n)
      (IBMSchwartzSecondProjection.weightedClass g a (tripleCoefficient n r 0) 1
        (firstChaosEmbedding (tripleCoefficient n r 1))) r :=
  observable_comp_hasDerivAt g a 0 (IBMQuarticSecondPrimitive.coefficient_zero_hasDerivAt n r)

theorem spatial_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    Continuous (spatial g a n) :=
  continuous_iff_continuousAt.mpr fun r => (spatial_hasDerivAt g a n r).continuousAt

theorem spatialLimit_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    Continuous (spatialLimit g a) :=
  (observable_continuous g a 0).comp
    (firstChaosEmbedding.toContinuousLinearMap.adjoint.continuous.comp sourceScenery_continuous)

theorem base_embedding (r : ℝ) :
    firstChaosEmbedding (baseCoefficient r) = sourceScenery r := by
  change firstChaosEmbedding (firstChaosEmbedding.toContinuousLinearMap.adjoint
    (firstChaosEmbedding (SeparableHilbertEmbedding.hilbertEmbedding
      FractionalSpectralKernel.SpectralSpace (IBMFiniteScenerySmoothing.direction r)))) = _
  rw [IBMQuarticSecondPrimitive.adjoint_embedding]
  rfl

/-- The terminal candidate uses the constructed Brownian scenery itself. -/
theorem spatialLimit_coeFn (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) :
    spatialLimit g a r =ᵐ[gaussianProduct] fun ω => g (a+sceneryPath ω r) := by
  filter_upwards [observable_coeFn g a 0 (baseCoefficient r),
    sceneryPath_coordinate_ae r] with ω ho hx
  change spatialLimit g a r ω = _ at ho
  rw [ho, base_embedding]
  change g (a+IBMSourceLaws.sceneryBase r ω) = g (a+sceneryPath ω r)
  rw [hx]

/-- For every fixed clock path, the source section is the actual IBM test
observable. No exceptional set uniform in all spatial points is asserted. -/
theorem actual_section (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (ωY : SampleSpace) :
    spatialLimit g a |clockPath ωY T| =ᵐ[gaussianProduct]
      fun ωX => g (a+ibmValue T (ωX,ωY)) :=
  spatialLimit_coeFn g a _

theorem spatial_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) :
    Tendsto (fun n => spatial g a n r) atTop (𝓝 (spatialLimit g a r)) :=
  (observable_continuous g a 0).continuousAt.tendsto.comp (coefficient_tendsto r)

def terminal (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : GaussianL2 :=
  ∫ ω, spatial g a n |clockPath ω T| ∂gaussianProduct

def terminalLimit (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : GaussianL2 :=
  ∫ ω, spatialLimit g a |clockPath ω T| ∂gaussianProduct

theorem terminal_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Integrable (fun ω => spatial g a n |clockPath ω T|) gaussianProduct := by
  apply (integrable_const (SchwartzMap.seminorm ℝ 0 0 (jet g 0))).mono'
    ((spatial_continuous g a n).stronglyMeasurable.comp_measurable
      (IBMQuarticClockTerminal.clockPosition_measurable T)).aestronglyMeasurable
  exact Eventually.of_forall fun ω => observable_bound g a 0 _

theorem terminalLimit_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => spatialLimit g a |clockPath ω T|) gaussianProduct := by
  apply (integrable_const (SchwartzMap.seminorm ℝ 0 0 (jet g 0))).mono'
    ((spatialLimit_continuous g a).stronglyMeasurable.comp_measurable
      (IBMQuarticClockTerminal.clockPosition_measurable T)).aestronglyMeasurable
  exact Eventually.of_forall fun ω => observable_bound g a 0 _

theorem terminal_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => terminal g a n T) atTop (𝓝 (terminalLimit g a T)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ => SchwartzMap.seminorm ℝ 0 0 (jet g 0))
  · intro n
    exact ((spatial_continuous g a n).stronglyMeasurable.comp_measurable
      (IBMQuarticClockTerminal.clockPosition_measurable T)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall fun ω => observable_bound g a 0 _
  · exact Eventually.of_forall fun ω => spatial_tendsto g a _

theorem origin_limit (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    spatialLimit g a 0 = g a • gaussianOne := by
  have hz : sourceScenery 0 = 0 := by
    apply norm_eq_zero.mp
    simpa using IBMRandomTimeHilbert.sourceScenery_norm_sq 0
  have hb : baseCoefficient 0 = 0 := by simp only [baseCoefficient, hz, map_zero]
  apply Lp.ext
  filter_upwards [observable_coeFn g a 0 (baseCoefficient 0),
    Lp.coeFn_smul (g a) gaussianOne, gaussianOne_coeFn,
    Lp.coeFn_zero ℝ 2 gaussianProduct] with ω ho hs h1 h0
  change spatialLimit g a 0 ω = _ at ho
  rw [ho, hs, Pi.smul_apply, h1, smul_eq_mul, mul_one, hb, map_zero, h0]
  simp [shiftedJet, jet]

/-- Strong convergence of the whole source-space candidate, rather than
separate convergence of finitely many chaos blocks. -/
theorem difference_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => terminal g a n T-spatial g a n 0) atTop
      (𝓝 (terminalLimit g a T-g a • gaussianOne)) := by
  simpa only [origin_limit] using (terminal_tendsto g a T).sub (spatial_tendsto g a 0)

/-- Both thresholds precede the varying source cutoff and mollifier index. -/
theorem uniform_source_tail (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N0 n0 : ℕ, ∀ N ≥ N0, ∀ n ≥ n0,
      ‖terminal g a n T-spatial g a n 0-
        truncation N (terminal g a n T-spatial g a n 0)‖ < ε := by
  let h := terminalLimit g a T-g a • gaussianOne
  obtain ⟨n0,hn⟩ := Metric.tendsto_atTop.mp (difference_tendsto g a T) (ε/4) (by positivity)
  obtain ⟨N0,hN⟩ := Metric.tendsto_atTop.mp (truncation_tendsto h) (ε/2) (by positivity)
  refine ⟨N0,n0,fun N hNN n hnn => ?_⟩
  have h1 : ‖terminal g a n T-spatial g a n 0-h‖ < ε/4 := by
    simpa only [dist_eq_norm] using hn n hnn
  have h2 : ‖h-truncation N h‖ < ε/2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hN N hNN
  have hb := IBMSchwartzSourceZeroTails.truncation_remainder_le N
    (terminal g a n T-spatial g a n 0) h
  linarith

end OperatorDerivativeRewrite.Foundation.IBMFullSchwartzTerminal
