import Foundation.IBMFoldedHeatPredictable
import Foundation.IBMSceneryClockIto

/-! Actual scalar clock Ito integrals of the explicit folded heat field.
Equality with the terminal IBM reconstruction still requires conditioning. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedHeatNativeIto
open InfiniteGaussian GaussianComplexHorizonIto IBMFoldedHeatPredictable
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance : MeasurableSpace (ℝ × SampleSpace) :=
  PredictableRealL2.predictable GaussianTimeProcess.naturalFiltration

def scalarInput (T : ℝ≥0) : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct) :=
  IBMSceneryClockIto.flatInput T (trim T)

def value (T : ℝ≥0) : Lp ℝ 2 IBMSourceLaws.jointMeasure :=
  IBMSceneryClockIto.jointIntegral T (scalarInput T)

theorem value_actual (T : ℝ≥0) :
    value T = IBMSpatialPointClockObstruction.realize (integralValue T) :=
  IBMSceneryClockIto.agreement T (trim T)

theorem native_sections (T : ℝ≥0) : ∀ᵐ X ∂gaussianProduct,
    (fun Y => value T (X,Y)) =ᵐ[gaussianProduct]
      GaussianPredictableHorizon.itoIntegral T
        (IBMSceneryClockIto.sectionPredictable T (scalarInput T) X) :=
  IBMSceneryClockIto.joint_sections_native T (scalarInput T)

theorem clock_mean_zero (T : ℝ≥0) : ∀ᵐ X ∂gaussianProduct,
    (∫ Y, value T (X,Y) ∂gaussianProduct) = 0 := by
  filter_upwards [native_sections T] with X hx
  rw [integral_congr_ae hx]
  exact GaussianPredictableHorizon.itoIntegral_centered T _

theorem value_energy (T : ℝ≥0) :
    ‖value T‖^2 = ∫ z, IBMFoldedHeatClockEnergy.raw T z ∂BrownianClockWeightedEnergy.base T := by
  rw [value_actual, IBMSpatialPointClockObstruction.realize.norm_map, integral_energy]

theorem native_section_energy (T : ℝ≥0) :
    (∫ X, ‖IBMSceneryClockIto.sectionPredictable T (scalarInput T) X‖^2 ∂gaussianProduct) =
      ∫ z, IBMFoldedHeatClockEnergy.raw T z ∂BrownianClockWeightedEnergy.base T := by
  rw [IBMSceneryClockIto.section_energy]
  have hn : ‖scalarInput T‖ = ‖value T‖ :=
    (IBMSceneryClockIto.jointIntegral_norm T (scalarInput T)).symm
  rw [hn, value_energy]

theorem canonical_agreement_iff (T : ℝ≥0) :
    value T = IBMSpatialTerminalReconstruction.canonicalValue T ↔
      trim T = IBMSpatialCanonicalAdjoint.representer T
        (IBMPhysicalNoiseClock.sourceKernel T) := by
  rw [value_actual]
  change IBMSpatialPointClockObstruction.realize
    (GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T (trim T)) =
      IBMSpatialPointClockObstruction.realize
        (GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T
          (IBMSpatialPredictableSteps.trim T
            (IBMSpatialTerminalReconstruction.canonicalInput T))) ↔ _
  rw [IBMSpatialTerminalReconstruction.canonicalInput, IBMSpatialCanonicalRepresentation.input,
    LinearIsometryEquiv.apply_symm_apply]
  constructor
  · intro h
    exact (GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T).injective
      (IBMSpatialPointClockObstruction.realize.injective h)
  · intro h
    rw [h]

theorem actual_reconstruction_of_coefficient (T : ℝ≥0)
    (h : trim T = IBMSpatialCanonicalAdjoint.representer T
      (IBMPhysicalNoiseClock.sourceKernel T)) :
    (fun w => value T w+IBMSpatialTerminalReconstruction.initialValue T w)
      =ᵐ[IBMSourceLaws.jointMeasure] IBMConstructedSources.ibmValue T := by
  rw [(canonical_agreement_iff T).mpr h]
  exact IBMSpatialTerminalReconstruction.actual_reconstruction T

end OperatorDerivativeRewrite.Foundation.IBMFoldedHeatNativeIto
