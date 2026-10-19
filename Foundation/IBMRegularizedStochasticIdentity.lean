import Foundation.GaussianSourceHorizonRegularization
import Foundation.IBMClockRegularizedSlope
import Foundation.GaussianObservedSecondRegularization

/-! The actual reflected IBM identity in a COMMON injective clock-number
topology, with a genuine source-valued predictable stochastic integrand. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRegularizedStochasticIdentity
open InfiniteGaussian GaussianClockValueOperators GaussianObservedSecondRegularization
open GaussianSourceHorizonRegularization GaussianSourceClockIto IBMSchwartzFullReflectedIto
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def smoothing : Field →L[ℝ] Field := clockLift commonSmoothing

theorem smoothing_injective : Function.Injective smoothing := by
  intro f g hfg
  apply eq_of_all_tests
  intro L
  apply commonSmoothing_injective
  have hh := congrArg (L.compLpL 2 gaussianProduct) hfg
  simpa only [smoothing,clockLift_test] using hh

theorem smoothing_integral (T : ℝ≥0) (u : Domain T) :
    smoothing (GaussianSourceClockIto.integral T u) =
      GaussianSourceClockIto.integral T (sourceRegularization T u) := by
  rw [integral_sourceRegularization]
  apply eq_of_all_tests
  intro L
  change L.compLpL 2 gaussianProduct (clockLift commonSmoothing
    (GaussianSourceClockIto.integral T u)) = _
  rw [clockLift_test,clockLift_test]
  change GaussianNumberSectors.projection 0 (L.compLpL 2 gaussianProduct
    (GaussianSourceClockIto.integral T u)) + GaussianInverseNumberPotential.potentialOperator
      (L.compLpL 2 gaussianProduct (GaussianSourceClockIto.integral T u)) = _
  rw [native_scalarization,realIto_projection_zero,zero_add]

/-- A genuine integrand in the original source-valued predictable domain. -/
def stochasticField (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : Domain T :=
  sourceRegularization T (integrand g a n T)

def correction (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : Field :=
  smoothing (IBMSchwartzBochnerDomain.wholeClass g a n T)

/-- Actual source-valued signed stochastic identity, including the original
origin/local-time and curvature correction. No expectation is taken. -/
theorem finite_mollifier_stochastic_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    smoothing (endpointClass g a n T) =
      GaussianSourceClockIto.integral T (stochasticField g a n T) + correction g a n T := by
  rw [finite_mollifier_identity,map_add]
  change smoothing (GaussianSourceClockIto.integral T (integrand g a n T)) +
    correction g a n T = _
  rw [smoothing_integral]
  rfl

theorem smoothed_endpoint_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => smoothing (endpointClass g a n T)) atTop
      (𝓝 (smoothing (endpointLimitClass g a T))) :=
  smoothing.continuous.tendsto _ |>.comp (endpointClass_tendsto g a T)

/-- The exact remaining convergence criterion, in the ACTUAL predictable
time-L2 norm. Fixed-time slope convergence alone is insufficient. -/
theorem correction_cauchy_iff_field (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    CauchySeq (fun n => correction g a n T) ↔ CauchySeq (fun n => stochasticField g a n T) := by
  have hI : CauchySeq (fun n => GaussianSourceClockIto.integral T (stochasticField g a n T)) ↔
      CauchySeq (fun n => stochasticField g a n T) := by
    simp only [Metric.cauchySeq_iff,(GaussianSourceClockIto.integral T).isometry.dist_eq]
  constructor
  · intro hC
    apply hI.mp
    obtain ⟨c,hc⟩ := cauchySeq_tendsto_of_complete hC
    have hh := ((smoothed_endpoint_tendsto g a T).sub hc).cauchySeq
    simpa only [finite_mollifier_stochastic_identity,add_sub_cancel_right] using hh
  · intro hU
    obtain ⟨i,hi⟩ := cauchySeq_tendsto_of_complete (hI.mpr hU)
    have hh := ((smoothed_endpoint_tendsto g a T).sub hi).cauchySeq
    simpa only [finite_mollifier_stochastic_identity,add_sub_cancel_left] using hh

/-- Once the genuine predictable fields converge, the correction limit and
full stochastic reconstruction follow with the specified common smoothing. -/
theorem correction_tendsto_of_field (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (u : Domain T) (hu : Tendsto (fun n => stochasticField g a n T) atTop (𝓝 u)) :
    Tendsto (fun n => correction g a n T) atTop
      (𝓝 (smoothing (endpointLimitClass g a T) - GaussianSourceClockIto.integral T u)) := by
  have hh := (smoothed_endpoint_tendsto g a T).sub
    ((GaussianSourceClockIto.integral T).continuous.tendsto _ |>.comp hu)
  simpa only [Function.comp_def,finite_mollifier_stochastic_identity,add_sub_cancel_left] using hh

end OperatorDerivativeRewrite.Foundation.IBMRegularizedStochasticIdentity
