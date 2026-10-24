import Foundation.IBMPhysicalClockAdjointBridge
import Foundation.GaussianClockBochnerContraction

/-! Physical scenery tests regularize the ACTUAL IBM point into the original
closed Gaussian clock derivative domain, with strong native graph convergence. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalSceneryTestClockGraph
open InfiniteGaussian IBMFirstSourceClockGraph IBMPhysicalWeakWiener
open IBMSchwartzWeakWienerClosure IBMPhysicalPointSlope GaussianClockBochnerContraction
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _

def projection (L : Tests) : ScalarSpace →L[ℝ] GaussianL2 := contract (testNoise L)

def gradientProjection (L : Tests) : VectorSpace →L[ℝ] GaussianVectorL2 := contract (testNoise L)

def point (t : ℝ≥0) (L : Tests) : GaussianL2 := projection L (IBMClockGraphDualLimit.point t)

def gradient (t : ℝ≥0) (L : Tests) : GaussianVectorL2 :=
  scalarTensor (IBMClockAverageCandidate.direction t) (evaluate L (slopeLimit t))

theorem projection_flip (u : ScalarSpace) (L : Tests) :
    projection L (flip u) = (innerSL ℝ (testNoise L)).compLpL 2 gaussianProduct u :=
  contract_flip gaussianProduct u (testNoise L)

theorem native_evaluation_eq (u : ScalarSpace) (L : Tests) :
    evaluate L (nativeField u) = (innerSL ℝ (testNoise L)).compLpL 2 gaussianProduct u := by
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.apply ℝ ℝ L).coeFn_compLpL (nativeField u),
    native.coeFn_compLpL u, (innerSL ℝ (testNoise L)).coeFn_compLpL u] with Y he hn hi
  change evaluate L (nativeField u) Y = nativeField u Y L at he
  change nativeField u Y = native (u Y) at hn
  rw [he, hn, native_apply, hi, innerSL_apply_apply, real_inner_comm]

theorem gradientProjection_native (n : ℕ) (t : ℝ≥0) (L : Tests) :
    gradientProjection L (clockGradient n t) =
      scalarTensor (IBMClockAverageCandidate.direction t)
        (evaluate L (nativeField (signedSource n t))) := by
  change contract (testNoise L)
    ((IBMClockAverageCandidate.tensorBilinear (IBMClockAverageCandidate.direction t)).compLp
      (flip (signedSource n t))) = _
  rw [contract_comp]
  change scalarTensor (IBMClockAverageCandidate.direction t)
    (projection L (flip (signedSource n t))) = _
  rw [projection_flip, native_evaluation_eq]

theorem native_value_tendsto (t : ℝ≥0) (L : Tests) :
    Tendsto (fun n => projection L (flip (IBMRandomTimeHilbert.randomMollifiedL2 n t)))
      atTop (nhds (point t L)) := by
  exact (projection L).continuous.tendsto _ |>.comp
    (flip.continuous.tendsto _ |>.comp (IBMRandomTimeHilbert.randomMollifiedL2_tendsto t))

theorem native_gradient_tendsto (t : ℝ≥0) (L : Tests) :
    Tendsto (fun n => gradientProjection L (clockGradient n t))
      atTop (nhds (gradient t L)) := by
  simp only [gradientProjection_native, gradient]
  exact (scalarTensor (IBMClockAverageCandidate.direction t)).continuous.tendsto _ |>.comp
    ((evaluate L).continuous.tendsto _ |>.comp (native_slope_tendsto t))

theorem point_graph (t : ℝ≥0) (ht : 0 < t) (L : Tests) :
    (point t L, gradient t L) ∈ closedCylindricalDerivative.graph := by
  apply closedCylindricalDerivative_isClosed.mem_of_tendsto
    ((native_value_tendsto t L).prodMk_nhds (native_gradient_tendsto t L))
  exact Eventually.of_forall fun n => contract_graph _ _
    (mollified_clock_graph n t ht) (testNoise L)

theorem point_mem (t : ℝ≥0) (ht : 0 < t) (L : Tests) :
    point t L ∈ closedCylindricalDerivative.domain :=
  LinearPMap.mem_domain_of_mem_graph (point_graph t ht L)

theorem derivative_value (t : ℝ≥0) (ht : 0 < t) (L : Tests) :
    closedCylindricalDerivative ⟨point t L, point_mem t ht L⟩ = gradient t L :=
  ((closedCylindricalDerivative.image_iff (point_mem t ht L)).mpr (point_graph t ht L)).symm

theorem randomSource_actual_ae (t : ℝ≥0) : ∀ᵐ Y ∂gaussianProduct,
    (IBMRandomTimeHilbert.randomSourceL2 t Y : SampleSpace → ℝ) =ᵐ[gaussianProduct]
      fun X => IBMConstructedSources.ibmValue t (X,Y) := by
  filter_upwards [(IBMRandomTimeHilbert.randomSourceClass_memLp t).coeFn_toLp,
    IBMConstructedSources.clockPath_coordinate_ae t] with Y hs hc
  change IBMRandomTimeHilbert.randomSourceL2 t Y = _ at hs
  rw [hs]
  change (IBMContinuousScenery.sourceScenery |GaussianTimeProcess.process t Y| :
    SampleSpace → ℝ) =ᵐ[gaussianProduct] _
  rw [← hc]
  exact (IBMConstructedSources.sceneryPath_coordinate_ae
    |IBMConstructedSources.clockPath Y t|).symm

/-- Literal ordinary scenery expectation of the ACTUAL IBM point, not a
new process postulated from a Gaussian kernel. -/
theorem point_actual_ae (t : ℝ≥0) (L : Tests) : point t L =ᵐ[gaussianProduct] fun Y =>
    ∫ X, IBMConstructedSources.ibmValue t (X,Y) * testNoise L X ∂gaussianProduct := by
  have hp : point t L =
      (innerSL ℝ (testNoise L)).compLpL 2 gaussianProduct (IBMRandomTimeHilbert.randomSourceL2 t) :=
    projection_flip _ L
  rw [hp]
  filter_upwards [(innerSL ℝ (testNoise L)).coeFn_compLpL
    (IBMRandomTimeHilbert.randomSourceL2 t), randomSource_actual_ae t] with Y hi hs
  rw [hi, innerSL_apply_apply, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [hs] with X hx
  rw [hx, Real.inner_apply, mul_comm]

theorem actual_scenery_product_integrable (t : ℝ≥0) (L : Tests) :
    ∀ᵐ Y ∂gaussianProduct, Integrable (fun X =>
      IBMConstructedSources.ibmValue t (X,Y) * testNoise L X) gaussianProduct := by
  filter_upwards [randomSource_actual_ae t] with Y hs
  apply ((Lp.memLp (IBMRandomTimeHilbert.randomSourceL2 t Y)).integrable_mul
    (Lp.memLp (testNoise L))).congr
  filter_upwards [hs] with X hx
  rw [Pi.mul_apply, hx]

end OperatorDerivativeRewrite.Foundation.IBMPhysicalSceneryTestClockGraph
