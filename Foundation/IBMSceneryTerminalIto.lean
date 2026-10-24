import Foundation.IBMSceneryClockIto

/-! Actual scalar parameterized clock integrals reconstruct the IBM terminal
value minus its scenery initial term, with original predictable-domain inputs. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSceneryTerminalIto
open InfiniteGaussian GaussianTimeHilbert GaussianComplexHorizonIto
open IBMSceneryClockIto IBMSpatialTerminalReconstruction
local instance : MeasurableSpace (ℝ × SampleSpace) :=
  PredictableRealL2.predictable GaussianTimeProcess.naturalFiltration
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
attribute [local instance] realPredictableL2_secondCountable predictableL2_secondCountable

def terminalInput (T : ℝ≥0) : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct) :=
  flatInput T (IBMSpatialPredictableSteps.trim T (canonicalInput T))

theorem terminal_integral (T : ℝ≥0) : jointIntegral T (terminalInput T) = canonicalValue T :=
  agreement T (IBMSpatialPredictableSteps.trim T (canonicalInput T))

theorem actual_identity (T : ℝ≥0) :
    (fun w => jointIntegral T (terminalInput T) w+initialValue T w) =ᵐ[IBMSourceLaws.jointMeasure]
      IBMConstructedSources.ibmValue T := by
  rw [terminal_integral]
  exact actual_reconstruction T

theorem initial_actual (T : ℝ≥0) : initialValue T =ᵐ[IBMSourceLaws.jointMeasure]
    fun w => IBMPhysicalNoiseRealization.physicalNoise (initialKernel T) w.1 := by
  change (fun w : IBMSourceLaws.JointSample => initialValue T w) =ᵐ[gaussianProduct.prod gaussianProduct]
    fun w => IBMPhysicalNoiseRealization.physicalNoise (initialKernel T) w.1
  have hm : Measurable (fun w : IBMSourceLaws.JointSample => initialValue T (w.2,w.1)) := by
    simpa only [Function.comp_def, Prod.swap] using
      (Lp.stronglyMeasurable (initialValue T)).measurable.comp measurable_swap
  have hn : Measurable (fun w : IBMSourceLaws.JointSample =>
      IBMPhysicalNoiseRealization.physicalNoise (initialKernel T) w.2) :=
    (Lp.stronglyMeasurable _).measurable.comp measurable_snd
  have h := (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm hn)).mpr (initial_sections T)
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp h
  simpa only [Function.comp_def, Prod.swap, Prod.mk.eta] using hs

theorem actual_native_sections (T : ℝ≥0) : ∀ᵐ X ∂gaussianProduct,
    (fun Y => IBMConstructedSources.ibmValue T (X,Y)-
      IBMPhysicalNoiseRealization.physicalNoise (initialKernel T) X) =ᵐ[gaussianProduct]
      GaussianPredictableHorizon.itoIntegral T (sectionPredictable T (terminalInput T) X) := by
  have hi : (fun w => jointIntegral T (terminalInput T) w) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => IBMConstructedSources.ibmValue T w-
        IBMPhysicalNoiseRealization.physicalNoise (initialKernel T) w.1 := by
    filter_upwards [actual_identity T, initial_actual T] with w hw hi
    rw [hi] at hw
    linarith
  filter_upwards [Measure.ae_ae_of_ae_prod hi, joint_sections_native T (terminalInput T)] with X ha hs
  filter_upwards [ha, hs] with Y ha hs
  linarith

theorem clock_mean_actual (T : ℝ≥0) : ∀ᵐ X ∂gaussianProduct,
    (∫ Y, IBMConstructedSources.ibmValue T (X,Y) ∂gaussianProduct) =
      IBMPhysicalNoiseRealization.physicalNoise (initialKernel T) X := by
  have hj : Integrable (IBMConstructedSources.ibmValue T) (gaussianProduct.prod gaussianProduct) :=
    ((Lp.memLp (IBMSpatialPointClockObstruction.realize (IBMPhysicalNoiseClock.sourceKernel T))).integrable
      (by norm_num)).congr (IBMSpatialPointClockObstruction.source_actual T)
  filter_upwards [hj.prod_right_ae, actual_native_sections T] with X hx ha
  have he := integral_congr_ae ha
  rw [integral_sub hx (integrable_const _), integral_const, probReal_univ, one_smul,
    GaussianPredictableHorizon.itoIntegral_centered] at he
  linarith

theorem terminal_energy (T : ℝ≥0) : ‖terminalInput T‖ = ‖canonicalInput T‖ := by
  rw [terminalInput, flatInput_norm, (IBMSpatialPredictableSteps.trim T).norm_map]

def finiteTerminalInput (r : ℕ) (T : ℝ≥0) : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct) :=
  flatInput T (IBMSpatialPredictableSteps.trim T (finiteInput r T))

theorem finite_input_tendsto (T : ℝ≥0) :
    Tendsto (fun r => finiteTerminalInput r T) atTop (𝓝 (terminalInput T)) :=
  ((flatInput T).continuous.comp (IBMSpatialPredictableSteps.trim T).continuous).continuousAt.tendsto.comp
    (IBMSpatialTerminalReconstruction.finite_input_tendsto T)

theorem finite_integral_tendsto (T : ℝ≥0) :
    Tendsto (fun r => jointIntegral T (finiteTerminalInput r T)) atTop (𝓝 (canonicalValue T)) := by
  have h := (jointIntegral T).continuous.continuousAt.tendsto.comp (finite_input_tendsto T)
  rw [terminal_integral] at h
  exact h

theorem terminal_physical_coefficient (T : ℝ≥0) (hT : 0 < T) (L : IBMPhysicalWeakWiener.Tests) :
    (innerSL ℝ (IBMPhysicalWeakWiener.testNoise L)).compLpL 2 (predictableMeasure T)
      (ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct (terminalInput T)) =
      trimEquiv T (GaussianRoughFiniteHorizon.restrictPredictable T
        (GaussianPredictableAdjoint.predictableProjection (IBMPhysicalSceneryTestClockGraph.gradient T L))) := by
  change (innerSL ℝ (IBMPhysicalWeakWiener.testNoise L)).compLpL 2 (predictableMeasure T)
    ((ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct)
      ((ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct).symm
        (noiseInput T (IBMSpatialPredictableSteps.trim T (canonicalInput T))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, noiseInput_test]
  exact physical_clark_ocone T hT L

end OperatorDerivativeRewrite.Foundation.IBMSceneryTerminalIto
