import Foundation.IBMFoldedPredictableProjection
import Foundation.IBMPhysicalSpatialInjection
import Foundation.IBMFoldedHeatNativeIto
import Foundation.IBMSceneryTerminalIto

/-! Unconditional identification of the explicit folded heat integrand with
the ORIGINAL canonical IBM terminal coefficient, at every positive horizon. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
open scoped NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedCanonicalIdentification
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianComplexHorizonIto
open IBMPhysicalWeakWiener IBMFoldedPhysicalPredictable IBMFoldedPredictableProjection
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

theorem trim_scalar (T : ℝ≥0) (L : Tests) :
    (L.comp IBMPhysicalNegativeEmbedding.embedding).compLpL 2 (predictableMeasure T)
      (IBMFoldedHeatPredictable.trim T) = trimEquiv T (finite T L) := by
  let : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
  apply Lp.ext
  apply ae_eq_trim_of_measurable (PredictableRealL2.predictable_le naturalFiltration)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  have ho := lpMeasToLpTrim_ae_eq (PredictableRealL2.predictable_le naturalFiltration)
    (IBMFoldedHeatPredictable.input T)
  have hp := lpMeasToLpTrim_ae_eq (PredictableRealL2.predictable_le naturalFiltration) (finite T L)
  filter_upwards [ae_eq_of_ae_eq_trim
    ((L.comp IBMPhysicalNegativeEmbedding.embedding).coeFn_compLpL
      (IBMFoldedHeatPredictable.trim T)),
    ho, hp,
    (L.comp IBMPhysicalNegativeEmbedding.embedding).coeFn_compLpL
      (IBMFoldedHeatPredictable.input T).val] with z hl ho hp hc
  change IBMFoldedHeatPredictable.trim T z = (IBMFoldedHeatPredictable.input T).val z at ho
  change trimEquiv T (finite T L) z = (finite T L).val z at hp
  change (finite T L).val z =
    (L.comp IBMPhysicalNegativeEmbedding.embedding) ((IBMFoldedHeatPredictable.input T).val z) at hc
  rw [hl, ho, hp]
  exact hc.symm

theorem physical_coefficient (T : ℝ≥0) (hT : 0 < T) (L : Tests) :
    (L.comp IBMPhysicalNegativeEmbedding.embedding).compLpL 2 (predictableMeasure T)
      (IBMFoldedHeatPredictable.trim T) =
    (L.comp IBMPhysicalNegativeEmbedding.embedding).compLpL 2 (predictableMeasure T)
      (IBMSpatialCanonicalAdjoint.representer T (IBMPhysicalNoiseClock.sourceKernel T)) := by
  rw [trim_scalar, finite_eq_adjoint T hT L, ← IBMSpatialCanonicalAdjoint.scalarAdjoint_eq,
    IBMSpatialCanonicalAdjoint.representer_dual,
    IBMSpatialTerminalReconstruction.physical_source_projection]

theorem canonical_input (T : ℝ≥0) (hT : 0 < T) :
    IBMFoldedHeatPredictable.trim T =
      IBMSpatialCanonicalAdjoint.representer T (IBMPhysicalNoiseClock.sourceKernel T) := by
  let : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
  apply IBMPhysicalSpatialInjection.compLp_injective (predictableMeasure T)
  apply IBMPhysicalMeasureSeparation.ext (predictableMeasure T)
  intro L
  have hc (U : Lp TimeHilbert 2 (predictableMeasure T)) :
      L.compLpL 2 (predictableMeasure T)
        (IBMPhysicalNegativeEmbedding.embedding.compLpL 2 (predictableMeasure T) U) =
      (L.comp IBMPhysicalNegativeEmbedding.embedding).compLpL 2 (predictableMeasure T) U := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLpL
      (IBMPhysicalNegativeEmbedding.embedding.compLpL 2 (predictableMeasure T) U),
      IBMPhysicalNegativeEmbedding.embedding.coeFn_compLpL U,
      (L.comp IBMPhysicalNegativeEmbedding.embedding).coeFn_compLpL U] with z hl he hc
    rw [hl,he,hc]
    rfl
  rw [hc,hc]
  exact physical_coefficient T hT L

theorem actual_reconstruction (T : ℝ≥0) (hT : 0 < T) :
    (fun w => IBMFoldedHeatNativeIto.value T w+IBMSpatialTerminalReconstruction.initialValue T w)
      =ᵐ[IBMSourceLaws.jointMeasure] IBMConstructedSources.ibmValue T :=
  IBMFoldedHeatNativeIto.actual_reconstruction_of_coefficient T (canonical_input T hT)

theorem native_value_eq_canonical (T : ℝ≥0) (hT : 0 < T) :
    IBMFoldedHeatNativeIto.value T = IBMSpatialTerminalReconstruction.canonicalValue T :=
  (IBMFoldedHeatNativeIto.canonical_agreement_iff T).mpr (canonical_input T hT)

theorem native_input_eq_terminal (T : ℝ≥0) (hT : 0 < T) :
    IBMFoldedHeatNativeIto.scalarInput T = IBMSceneryTerminalIto.terminalInput T := by
  change IBMSceneryClockIto.flatInput T (IBMFoldedHeatPredictable.trim T) =
    IBMSceneryClockIto.flatInput T
      (IBMSpatialPredictableSteps.trim T (IBMSpatialTerminalReconstruction.canonicalInput T))
  rw [canonical_input T hT, IBMSpatialTerminalReconstruction.canonicalInput,
    IBMSpatialCanonicalRepresentation.input, LinearIsometryEquiv.apply_symm_apply]

theorem finite_scalar_inputs_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun r => IBMSceneryTerminalIto.finiteTerminalInput r T) atTop
      (𝓝 (IBMFoldedHeatNativeIto.scalarInput T)) := by
  rw [native_input_eq_terminal T hT]
  exact IBMSceneryTerminalIto.finite_input_tendsto T

theorem actual_native_sections (T : ℝ≥0) (hT : 0 < T) : ∀ᵐ X ∂gaussianProduct,
    (fun Y => IBMConstructedSources.ibmValue T (X,Y)-
      IBMPhysicalNoiseRealization.physicalNoise
        (IBMSpatialTerminalReconstruction.initialKernel T) X)
      =ᵐ[gaussianProduct] GaussianPredictableHorizon.itoIntegral T
        (IBMSceneryClockIto.sectionPredictable T (IBMFoldedHeatNativeIto.scalarInput T) X) := by
  rw [native_input_eq_terminal T hT]
  exact IBMSceneryTerminalIto.actual_native_sections T

end OperatorDerivativeRewrite.Foundation.IBMFoldedCanonicalIdentification
