import Foundation.IBMSchwartzSpatialPrimitive
import Foundation.IBMQuarticClockTerminal

/-! Strong source-L2 and actual clock-averaged limits of the nonlinear
Schwartz primitive. Heat reconstruction is a separate obligation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzPrimitiveLimit
open InfiniteGaussian IBMCorrectionStein IBMShiftedJetMoments IBMGaussianMeanDerivative
open IBMSchwartzSpatialPrimitive IBMConstructedSources IBMContinuousScenery

theorem primitive_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) : Continuous (primitive g a) := by
  have hq : Continuous (fun u : CoefficientSpace => M g a u 2 0) :=
    continuous_iff_continuousAt.mpr fun u => (mean_hasFDerivAt g a u 2).continuousAt
  exact (hq.div_const 2).smul (GaussianWickContinuity.wick_continuous 2)

/-- The actual projected bounded observable gives a global bound, uniform
in the source direction and therefore in the mollifier and radius. -/
theorem primitive_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) :
    ‖primitive g a u‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g 0) := by
  rw [primitive_eq_projection]
  exact IBMHigherScalarProjection.bounded_projection_norm u 2
    (shiftedJet_smooth g a 0).continuous (shiftedJet_bound g a 0)

theorem spatialPrimitive_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    Continuous (spatialPrimitive g a n) :=
  continuous_iff_continuousAt.mpr fun r => (spatialPrimitive_hasDerivAt g a n r).continuousAt

def limitPrimitive (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) : GaussianL2 :=
  primitive g a (IBMQuarticPrimitiveLimit.baseCoefficient r)

theorem spatialPrimitive_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) :
    Tendsto (fun n => spatialPrimitive g a n r) atTop (𝓝 (limitPrimitive g a r)) :=
  (primitive_continuous g a).continuousAt.tendsto.comp (IBMQuarticPrimitiveLimit.coefficient_tendsto r)

theorem limitPrimitive_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    Continuous (limitPrimitive g a) :=
  (primitive_continuous g a).comp
    (firstChaosEmbedding.toContinuousLinearMap.adjoint.continuous.comp sourceScenery_continuous)

theorem limitPrimitive_zero (g : SchwartzMap ℝ ℝ) (a : ℝ) : limitPrimitive g a 0 = 0 := by
  have hz : sourceScenery 0 = 0 := by
    apply norm_eq_zero.mp
    simpa using IBMRandomTimeHilbert.sourceScenery_norm_sq 0
  simp only [limitPrimitive, IBMQuarticPrimitiveLimit.baseCoefficient, hz, map_zero, primitive,
    IBMScalarSecondProjection.wick_two_zero, smul_zero]

def terminalMean (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : GaussianL2 :=
  ∫ ω, spatialPrimitive g a n |clockPath ω T| ∂gaussianProduct

def terminalLimit (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : GaussianL2 :=
  ∫ ω, limitPrimitive g a |clockPath ω T| ∂gaussianProduct

theorem terminal_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Integrable (fun ω => spatialPrimitive g a n |clockPath ω T|) gaussianProduct := by
  apply (integrable_const (SchwartzMap.seminorm ℝ 0 0 (jet g 0))).mono'
    ((spatialPrimitive_continuous g a n).stronglyMeasurable.comp_measurable
      (IBMQuarticClockTerminal.clockPosition_measurable T)).aestronglyMeasurable
  exact Eventually.of_forall fun ω => primitive_bound g a _

theorem limit_terminal_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => limitPrimitive g a |clockPath ω T|) gaussianProduct := by
  apply (integrable_const (SchwartzMap.seminorm ℝ 0 0 (jet g 0))).mono'
    ((limitPrimitive_continuous g a).stronglyMeasurable.comp_measurable
      (IBMQuarticClockTerminal.clockPosition_measurable T)).aestronglyMeasurable
  exact Eventually.of_forall fun ω => primitive_bound g a _

theorem terminalMean_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => terminalMean g a n T) atTop (𝓝 (terminalLimit g a T)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ => SchwartzMap.seminorm ℝ 0 0 (jet g 0))
  · intro n
    exact ((spatialPrimitive_continuous g a n).stronglyMeasurable.comp_measurable
      (IBMQuarticClockTerminal.clockPosition_measurable T)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall fun ω => primitive_bound g a _
  · exact Eventually.of_forall fun ω => spatialPrimitive_tendsto g a _

theorem terminal_difference_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => terminalMean g a n T-spatialPrimitive g a n 0) atTop
      (𝓝 (terminalLimit g a T)) := by
  simpa only [limitPrimitive_zero, sub_zero] using
    (terminalMean_tendsto g a T).sub (spatialPrimitive_tendsto g a 0)

end OperatorDerivativeRewrite.Foundation.IBMSchwartzPrimitiveLimit
