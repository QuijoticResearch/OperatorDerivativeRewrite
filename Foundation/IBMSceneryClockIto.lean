import Foundation.GaussianCrossParameterizedIto
import Foundation.IBMSpatialTerminalReconstruction

/-! Actual scenery white noise commutes with the ORIGINAL parameter-Ito map.
The scalar product integral retains the original predictable clock measure. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSceneryClockIto
open InfiniteGaussian GaussianTimeHilbert GaussianComplexHorizonIto
open IBMPhysicalNoiseRealization IBMSpatialPointClockObstruction
local instance : MeasurableSpace (ℝ × SampleSpace) :=
  PredictableRealL2.predictable GaussianTimeProcess.naturalFiltration
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
attribute [local instance] realPredictableL2_secondCountable predictableL2_secondCountable

def noiseInput (T : ℝ≥0) : Lp TimeHilbert 2 (predictableMeasure T) →ₗᵢ[ℝ]
    Lp GaussianL2 2 (predictableMeasure T) :=
  BochnerLinearIsometry.lift (predictableMeasure T) physicalNoise

def flatInput (T : ℝ≥0) : Lp TimeHilbert 2 (predictableMeasure T) →ₗᵢ[ℝ]
    Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct) :=
  (ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct).symm.toLinearIsometry.comp
    (noiseInput T)

def jointIntegral (T : ℝ≥0) : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct) →ₗᵢ[ℝ]
    Lp ℝ 2 IBMSourceLaws.jointMeasure :=
  (ProductL2Curry.swap gaussianProduct gaussianProduct).comp
    (GaussianParameterizedIto.realFlat gaussianProduct T)

def inputSections (T : ℝ≥0) (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) :
    Lp (Lp ℝ 2 (predictableMeasure T)) 2 gaussianProduct :=
  ProductL2Curry.flip (predictableMeasure T) gaussianProduct
    (ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct h)

theorem flatInput_norm (T : ℝ≥0) (u : Lp TimeHilbert 2 (predictableMeasure T)) :
    ‖flatInput T u‖ = ‖u‖ := (flatInput T).norm_map u

theorem jointIntegral_norm (T : ℝ≥0)
    (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) :
    ‖jointIntegral T h‖ = ‖h‖ := (jointIntegral T).norm_map h

theorem noise_integral (T : ℝ≥0) (u : Lp TimeHilbert 2 (predictableMeasure T)) :
    IBMClockPhysicalOccupation.noiseLift
      (GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T u) =
        GaussianParameterizedIto.realIntegral gaussianProduct T (noiseInput T u) :=
  GaussianCrossParameterizedIto.realIntegral_map (volume : Measure ℝ) gaussianProduct T
    physicalNoise.toContinuousLinearMap u

theorem agreement (T : ℝ≥0) (u : Lp TimeHilbert 2 (predictableMeasure T)) :
    jointIntegral T (flatInput T u) =
      realize (GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T u) := by
  have hc : jointIntegral T (flatInput T u) =
      ProductL2Curry.swap gaussianProduct gaussianProduct
        ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
          (GaussianParameterizedIto.realIntegral gaussianProduct T (noiseInput T u))) := by
    change ProductL2Curry.swap gaussianProduct gaussianProduct
      ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
        (GaussianParameterizedIto.realIntegral gaussianProduct T
          ((ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct)
            ((ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct).symm
              (noiseInput T u))))) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  rw [hc]
  change ProductL2Curry.swap gaussianProduct gaussianProduct
    ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
      (GaussianParameterizedIto.realIntegral gaussianProduct T (noiseInput T u))) =
    ProductL2Curry.swap gaussianProduct gaussianProduct
      ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
        (IBMClockPhysicalOccupation.noiseLift
          (GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T u)))
  rw [noise_integral]

theorem joint_curry (T : ℝ≥0)
    (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) :
    ProductL2Curry.curryEquiv gaussianProduct gaussianProduct (jointIntegral T h) =
      BochnerLinearIsometry.lift gaussianProduct (realIto T) (inputSections T h) := by
  change ProductL2Curry.flip gaussianProduct gaussianProduct
    (ProductL2Curry.flip gaussianProduct gaussianProduct
      (BochnerLinearIsometry.lift gaussianProduct (realIto T) (inputSections T h))) = _
  exact GaussianClockBochnerContraction.flip_involution gaussianProduct _

theorem joint_sections (T : ℝ≥0)
    (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) : ∀ᵐ X ∂gaussianProduct,
    (fun Y => jointIntegral T h (X,Y)) =ᵐ[gaussianProduct] realIto T (inputSections T h X) := by
  have hc := ProductL2Curry.curry_coeFn gaussianProduct gaussianProduct (jointIntegral T h)
  change ∀ᵐ X ∂gaussianProduct,
    ProductL2Curry.curryEquiv gaussianProduct gaussianProduct (jointIntegral T h) X =ᵐ[gaussianProduct]
      (fun Y => jointIntegral T h (X,Y)) at hc
  rw [joint_curry] at hc
  filter_upwards [hc, BochnerLinearIsometry.lift_coeFn gaussianProduct (realIto T)
    (inputSections T h)] with X hc hl
  rw [hl] at hc
  exact hc.symm

def sectionPredictable (T : ℝ≥0)
    (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) (X : SampleSpace) :
    GaussianPredictableHorizon.PredictableDomain T :=
  (trimEquiv T).symm (inputSections T h X)

theorem joint_sections_native (T : ℝ≥0)
    (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) : ∀ᵐ X ∂gaussianProduct,
    (fun Y => jointIntegral T h (X,Y)) =ᵐ[gaussianProduct]
      GaussianPredictableHorizon.itoIntegral T (sectionPredictable T h X) :=
  joint_sections T h

theorem section_energy (T : ℝ≥0)
    (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) :
    (∫ X, ‖sectionPredictable T h X‖^2 ∂gaussianProduct) = ‖h‖^2 := by
  have hn : ‖inputSections T h‖ = ‖h‖ := by
    rw [inputSections, (ProductL2Curry.flip (predictableMeasure T) gaussianProduct).norm_map,
      (ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct).norm_map]
  calc
    _ = ∫ X, ‖inputSections T h X‖^2 ∂gaussianProduct := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun X => by
        change ‖(trimEquiv T).symm (inputSections T h X)‖^2 = ‖inputSections T h X‖^2
        rw [(trimEquiv T).symm.norm_map])
    _ = ‖inputSections T h‖^2 := (BochnerL2Dominated.norm_sq_integral _).symm
    _ = _ := by rw [hn]

theorem noiseInput_test (T : ℝ≥0) (u : Lp TimeHilbert 2 (predictableMeasure T))
    (L : IBMPhysicalWeakWiener.Tests) :
    (innerSL ℝ (IBMPhysicalWeakWiener.testNoise L)).compLpL 2 (predictableMeasure T)
      (noiseInput T u) =
        (L.comp IBMPhysicalNegativeEmbedding.embedding).compLpL 2 (predictableMeasure T) u := by
  apply Lp.ext
  filter_upwards [(innerSL ℝ (IBMPhysicalWeakWiener.testNoise L)).coeFn_compLpL (noiseInput T u),
    BochnerLinearIsometry.lift_coeFn (predictableMeasure T) physicalNoise u,
    (L.comp IBMPhysicalNegativeEmbedding.embedding).coeFn_compLpL u] with z hi hn hl
  change noiseInput T u z = _ at hn
  rw [hi, hn, hl, innerSL_apply_apply, real_inner_comm]
  exact IBMPhysicalWeakWiener.actual_pairing (u z) L

end OperatorDerivativeRewrite.Foundation.IBMSceneryClockIto
