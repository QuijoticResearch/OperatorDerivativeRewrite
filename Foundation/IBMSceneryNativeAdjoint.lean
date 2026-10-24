import Foundation.IBMFoldedCanonicalIdentification
import Foundation.BochnerLiftAdjointInclusion
import Foundation.IBMIntrinsicOperators

/-! Native clock integrals with an L2 scenery parameter belong to the ORIGINAL
ambient clock divergence domain. Intrinsic restriction retains its observable
projection; no observed-filtration representation is asserted. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSceneryNativeAdjoint
open InfiniteGaussian GaussianComplexHorizonIto IBMIntrinsicOperators
open IBMFiniteAverageCore
local instance : MeasurableSpace (ℝ × SampleSpace) :=
  PredictableRealL2.predictable GaussianTimeProcess.naturalFiltration
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local instance] realPredictableL2_secondCountable
local instance : CompleteSpace IBMTimeAveragedObservable.IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

def nativeField (T : ℝ≥0) : Lp ℝ 2 (predictableMeasure T) →ₗᵢ[ℝ] GaussianVectorL2 :=
  GaussianPredictableAdjoint.predictableField.comp
    ((GaussianFiniteHorizonAdjoint.extendPredictable T).comp
      (trimEquiv T).symm.toLinearIsometry)

theorem native_graph (T : ℝ≥0) (u : Lp ℝ 2 (predictableMeasure T)) :
    (nativeField T u, realIto T u) ∈ hilbertDivergence.graph := by
  have h := GaussianPredictableAdjoint.predictableField_divergence_graph
    (GaussianFiniteHorizonAdjoint.extendPredictable T ((trimEquiv T).symm u))
  rw [← GaussianFiniteHorizonAdjoint.finite_integral_eq_extended] at h
  exact h

def field (T : ℝ≥0)
    (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) : FieldSpace :=
  BochnerLinearIsometry.lift gaussianProduct (nativeField T)
    (IBMSceneryClockIto.inputSections T h)

theorem partial_graph (T : ℝ≥0)
    (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) :
    (field T h, clockUnitary (IBMSceneryClockIto.jointIntegral T h)) ∈
      partialDerivative.adjoint.graph := by
  apply LinearPMap.le_graph_of_le
    (BochnerLiftAdjointInclusion.lift_adjoint_le gaussianProduct
      closedCylindricalDerivative closedCylindricalDerivative_dense_domain)
  rw [BochnerClosedOperator.mem_lift_graph_iff]
  change ∀ᵐ X ∂gaussianProduct,
    (field T h X, ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
      (IBMSceneryClockIto.jointIntegral T h) X) ∈ hilbertDivergence.graph
  rw [IBMSceneryClockIto.joint_curry]
  filter_upwards [BochnerLinearIsometry.lift_coeFn gaussianProduct (nativeField T)
    (IBMSceneryClockIto.inputSections T h),
    BochnerLinearIsometry.lift_coeFn gaussianProduct (realIto T)
      (IBMSceneryClockIto.inputSections T h)] with X hf hi
  change field T h X = _ at hf
  rw [hf, hi]
  exact native_graph T _

theorem clock_mem (T : ℝ≥0)
    (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) :
    field T h ∈ clockDerivative.adjoint.domain := by
  rw [clock_adjoint_domain]
  exact LinearPMap.mem_domain_of_mem_graph (partial_graph T h)

theorem clock_value (T : ℝ≥0)
    (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) :
    clockDerivative.adjoint ⟨field T h, clock_mem T h⟩ =
      IBMSceneryClockIto.jointIntegral T h := by
  have hp := LinearPMap.mem_domain_of_mem_graph (partial_graph T h)
  rw [clock_adjoint_apply _ (clock_mem T h) hp,
    ((partialDerivative.adjoint.image_iff hp).mpr (partial_graph T h)).symm,
    LinearIsometryEquiv.symm_apply_apply]

theorem field_norm (T : ℝ≥0)
    (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) :
    ‖field T h‖ = ‖h‖ := by
  rw [field, (BochnerLinearIsometry.lift gaussianProduct (nativeField T)).norm_map]
  rw [IBMSceneryClockIto.inputSections,
    (ProductL2Curry.flip (predictableMeasure T) gaussianProduct).norm_map,
    (ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct).norm_map]

theorem intrinsic_value (T : ℝ≥0)
    (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) :
    ∃ hi : field T h ∈ intrinsicClock.adjoint.domain,
      intrinsicClock.adjoint ⟨field T h, hi⟩ =
        IBMTimeAveragedObservable.IntrinsicSpace.orthogonalProjectionOnto
          (IBMSceneryClockIto.jointIntegral T h) := by
  refine ⟨clock_source_divergence_mem ⟨_, clock_mem T h⟩, ?_⟩
  exact (intrinsic_clock_divergence_value ⟨_, clock_mem T h⟩).trans
    (congrArg IBMTimeAveragedObservable.IntrinsicSpace.orthogonalProjectionOnto
      (clock_value T h))

theorem finite_fields_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Filter.Tendsto (fun r => field T (IBMSceneryTerminalIto.finiteTerminalInput r T))
      Filter.atTop (nhds (field T (IBMFoldedHeatNativeIto.scalarInput T))) := by
  have hc : Continuous (field T) :=
    (BochnerLinearIsometry.lift gaussianProduct (nativeField T)).continuous.comp
      ((ProductL2Curry.flip (predictableMeasure T) gaussianProduct).continuous.comp
        (ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct).continuous)
  exact (hc.tendsto _).comp
    (IBMFoldedCanonicalIdentification.finite_scalar_inputs_tendsto T hT)

theorem folded_value (T : ℝ≥0) (hT : 0 < T) :
    clockDerivative.adjoint
      ⟨field T (IBMFoldedHeatNativeIto.scalarInput T),
        clock_mem T (IBMFoldedHeatNativeIto.scalarInput T)⟩ +
      IBMSpatialTerminalReconstruction.initialValue T =
        IBMSpatialTerminalReconstruction.canonicalValue T +
          IBMSpatialTerminalReconstruction.initialValue T := by
  rw [clock_value]
  exact congrArg (fun v => v + IBMSpatialTerminalReconstruction.initialValue T)
    (IBMFoldedCanonicalIdentification.native_value_eq_canonical T hT)

theorem actual_folded_value (T : ℝ≥0) (hT : 0 < T) :
    (fun w => clockDerivative.adjoint
      ⟨field T (IBMFoldedHeatNativeIto.scalarInput T),
        clock_mem T (IBMFoldedHeatNativeIto.scalarInput T)⟩ w +
      IBMSpatialTerminalReconstruction.initialValue T w)
        =ᵐ[IBMSourceLaws.jointMeasure] IBMConstructedSources.ibmValue T := by
  rw [clock_value]
  exact IBMFoldedCanonicalIdentification.actual_reconstruction T hT

end OperatorDerivativeRewrite.Foundation.IBMSceneryNativeAdjoint
