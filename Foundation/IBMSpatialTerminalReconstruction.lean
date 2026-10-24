import Foundation.IBMSpatialCanonicalRepresentation
import Foundation.IBMSpatialPointClockObstruction
import Foundation.IBMPhysicalSceneryTestClockGraph

/-! Actual IBM terminal values: canonical ordinary spatial clock integrals,
with their initial-scenery mean and genuine finite-width input convergence. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialTerminalReconstruction
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess
open IBMPhysicalNoiseClock IBMPhysicalNoiseVectors IBMPhysicalNoiseCalculus
open IBMSpatialCanonicalAdjoint IBMSpatialCanonicalRepresentation IBMSpatialPointClockObstruction
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

theorem source_past (T : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration T] (sourceKernel T) gaussianProduct := by
  have hm : AEStronglyMeasurable[naturalFiltration T]
      (fun Y => vector |process T Y|) gaussianProduct :=
    (vector_continuous.stronglyMeasurable.comp_measurable
      (continuous_abs.measurable.comp (process_stronglyAdapted T).measurable)).aestronglyMeasurable
  apply hm.congr
  filter_upwards [sourceKernel_ae T, IBMConstructedSources.clockPath_coordinate_ae T] with Y hs hc
  rw [hs, hc]

theorem mollified_past (r : ℕ) (T : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration T] (mollifiedKernel r T) gaussianProduct := by
  have hm : AEStronglyMeasurable[naturalFiltration T]
      (IBMRandomTimeHilbert.randomMollifiedL2 r T) gaussianProduct :=
    (((IBMRandomTimeHilbert.mollifiedScenery_continuous r).stronglyMeasurable.comp_measurable
      (continuous_abs.measurable.comp (process_stronglyAdapted T).measurable)).aestronglyMeasurable).congr
        (IBMRandomTimeHilbert.randomMollifiedClass_memLp r T).coeFn_toLp.symm
  exact (kernelPullback.continuous.comp_aestronglyMeasurable hm).congr
    (kernelPullback.coeFn_compLpL (IBMRandomTimeHilbert.randomMollifiedL2 r T)).symm

theorem endpoint_past (r : ℕ) (T : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration T] (endpoint r T) gaussianProduct := by
  have hc : AEStronglyMeasurable[naturalFiltration T]
      (Lp.const 2 gaussianProduct (convolutionKernel (IBMMollifier.kernel r) 0)) gaussianProduct :=
    stronglyMeasurable_const.aestronglyMeasurable.congr
      (Lp.coeFn_const 2 gaussianProduct _).symm
  exact ((mollified_past r T).sub hc).congr (Lp.coeFn_sub _ _).symm

def canonicalInput (T : ℝ≥0) : IBMSpatialPredictableSteps.Domain T :=
  input T (sourceKernel T)

def initialKernel (T : ℝ≥0) : TimeHilbert := mean (sourceKernel T)

def initialValue (T : ℝ≥0) : Lp ℝ 2 IBMSourceLaws.jointMeasure :=
  realize (Lp.const 2 gaussianProduct (initialKernel T))

def canonicalValue (T : ℝ≥0) : Lp ℝ 2 IBMSourceLaws.jointMeasure :=
  realize (IBMSpatialPredictableSteps.integral T (canonicalInput T))

theorem canonical_integral (T : ℝ≥0) :
    IBMSpatialPredictableSteps.integral T (canonicalInput T) =
      sourceKernel T-Lp.const 2 gaussianProduct (initialKernel T) :=
  integral_input T (sourceKernel T) (source_past T)

theorem canonical_identity (T : ℝ≥0) :
    canonicalValue T+initialValue T = realize (sourceKernel T) := by
  rw [canonicalValue, canonical_integral, map_sub]
  change realize (sourceKernel T)-initialValue T+initialValue T = _
  abel

theorem actual_reconstruction (T : ℝ≥0) :
    (fun w => canonicalValue T w+initialValue T w) =ᵐ[IBMSourceLaws.jointMeasure]
      IBMConstructedSources.ibmValue T := by
  have h := Lp.coeFn_add (canonicalValue T) (initialValue T)
  rw [canonical_identity] at h
  exact h.symm.trans (source_actual T)

theorem initial_sections (T : ℝ≥0) : ∀ᵐ Y ∂InfiniteGaussian.gaussianProduct,
    (fun X => initialValue T (X,Y)) =ᵐ[InfiniteGaussian.gaussianProduct]
      IBMPhysicalNoiseRealization.physicalNoise (initialKernel T) := by
  filter_upwards [realize_sections (Lp.const 2 gaussianProduct (initialKernel T)),
    Lp.coeFn_const 2 gaussianProduct (initialKernel T)] with Y hs hc
  simpa only [hc, Function.const_apply, initialValue] using hs

def finiteInput (r : ℕ) (T : ℝ≥0) : IBMSpatialPredictableSteps.Domain T :=
  input T (endpoint r T)

theorem finite_integral (r : ℕ) (T : ℝ≥0) :
    IBMSpatialPredictableSteps.integral T (finiteInput r T) = center (endpoint r T) :=
  integral_input T (endpoint r T) (endpoint_past r T)

theorem finite_input_tendsto (T : ℝ≥0) :
    Tendsto (fun r => finiteInput r T) atTop (𝓝 (canonicalInput T)) :=
  (IBMSpatialPredictableSteps.trim T).symm.continuous.continuousAt.tendsto.comp
    ((representer T).continuous.continuousAt.tendsto.comp (endpoint_tendsto T))

theorem finite_joint_tendsto (T : ℝ≥0) :
    Tendsto (fun r => realize (IBMSpatialPredictableSteps.integral T (finiteInput r T))) atTop
      (𝓝 (canonicalValue T)) := by
  have h := ((GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T).continuous.comp
    (IBMSpatialPredictableSteps.trim T).continuous).continuousAt.tendsto.comp (finite_input_tendsto T)
  exact realize.continuous.continuousAt.tendsto.comp h

theorem finite_input_eventually_ne_running (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ r : ℕ in atTop, finiteInput r T ≠ IBMSpatialPointClockEnergy.input r T := by
  have hb := (finite_input_tendsto T).norm.eventually
    (gt_mem_nhds (lt_add_one ‖canonicalInput T‖))
  have he := (IBMSpatialPointClockEnergy.integral_norm_escape T hT).eventually
    (eventually_ge_atTop (‖canonicalInput T‖+1))
  filter_upwards [hb, he] with r hb he
  intro h
  have hn : ‖finiteInput r T‖ = ‖IBMSpatialPointClockEnergy.integralValue r T‖ := by
    calc
      _ = ‖IBMSpatialPredictableSteps.integral T (finiteInput r T)‖ := by
        rw [IBMSpatialPredictableSteps.integral,
          (GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T).norm_map,
          (IBMSpatialPredictableSteps.trim T).norm_map]
      _ = ‖IBMSpatialPredictableSteps.integral T (IBMSpatialPointClockEnergy.input r T)‖ := by rw [h]
      _ = _ := rfl
  rw [hn] at hb
  exact (not_lt_of_ge he) hb

theorem physical_source_projection (T : ℝ≥0) (L : IBMPhysicalWeakWiener.Tests) :
    (L.comp IBMPhysicalNegativeEmbedding.embedding).compLpL 2 gaussianProduct (sourceKernel T) =
      IBMPhysicalSceneryTestClockGraph.point T L := by
  apply Lp.ext
  filter_upwards [(L.comp IBMPhysicalNegativeEmbedding.embedding).coeFn_compLpL (sourceKernel T),
    IBMPhysicalSceneryTestClockGraph.point_actual_ae T L, sourceKernel_actual_realization T]
    with Y ha hp hs
  rw [ha, hp]
  change L (IBMPhysicalNegativeEmbedding.embedding (sourceKernel T Y)) = _
  calc
    _ = ∫ X, IBMPhysicalNoiseRealization.physicalNoise (sourceKernel T Y) X *
        IBMPhysicalWeakWiener.testNoise L X ∂gaussianProduct :=
      (IBMPhysicalWeakWiener.expectation_pairing (sourceKernel T Y) L).symm
    _ = _ := integral_congr_ae (hs.mono (fun X hx =>
      congrArg (fun z => z*IBMPhysicalWeakWiener.testNoise L X) hx))

theorem physical_clark_ocone (T : ℝ≥0) (hT : 0 < T) (L : IBMPhysicalWeakWiener.Tests) :
    (L.comp IBMPhysicalNegativeEmbedding.embedding).compLpL 2
      (GaussianComplexHorizonIto.predictableMeasure T)
        (IBMSpatialPredictableSteps.trim T (canonicalInput T)) =
      GaussianComplexHorizonIto.trimEquiv T
        (GaussianRoughFiniteHorizon.restrictPredictable T
          (GaussianPredictableAdjoint.predictableProjection
            (IBMPhysicalSceneryTestClockGraph.gradient T L))) := by
  rw [canonicalInput, IBMSpatialCanonicalRepresentation.input,
    LinearIsometryEquiv.apply_symm_apply, representer_dual, physical_source_projection,
    scalarAdjoint_eq]
  have h := GaussianFiniteHorizonAdjoint.finiteAdjoint_on_full_derivative T
    ⟨IBMPhysicalSceneryTestClockGraph.point T L, IBMPhysicalSceneryTestClockGraph.point_mem T hT L⟩
  rw [IBMPhysicalSceneryTestClockGraph.derivative_value T hT L] at h
  exact congrArg (GaussianComplexHorizonIto.trimEquiv T) h

end OperatorDerivativeRewrite.Foundation.IBMSpatialTerminalReconstruction
