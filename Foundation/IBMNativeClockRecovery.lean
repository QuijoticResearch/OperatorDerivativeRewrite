import Foundation.IBMSchwartzHeatReconstruction

/-! A single bounded original predictable-adjoint map recovers every actual
finite-horizon native clock field from its integral value. This identifies
the existing fields; it does not select a new Gaussian inverse. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMNativeClockRecovery
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open GaussianPredictableAdjoint GaussianComplexHorizonIto
local instance : MeasurableSpace (ℝ × SampleSpace) :=
  PredictableRealL2.predictable GaussianTimeProcess.naturalFiltration
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] realPredictableL2_secondCountable

def scalar : GaussianL2 →L[ℝ] GaussianVectorL2 :=
  predictableField.toContinuousLinearMap.comp predictableAdjoint

theorem scalar_native (T : ℝ≥0) (u : Lp ℝ 2 (predictableMeasure T)) :
    scalar (GaussianComplexHorizonIto.realIto T u) =
      IBMSceneryNativeAdjoint.nativeField T u := by
  change predictableField (predictableAdjoint
    (GaussianPredictableHorizon.itoIntegral T ((trimEquiv T).symm u))) =
    predictableField (GaussianFiniteHorizonAdjoint.extendPredictable T ((trimEquiv T).symm u))
  rw [GaussianFiniteHorizonAdjoint.finite_integral_eq_extended,
    predictableAdjoint_integral]

def joint : JointL2 →L[ℝ] FieldSpace :=
  (scalar.compLpL 2 gaussianProduct).comp
    clockUnitary.toLinearIsometry.toContinuousLinearMap

theorem joint_native (T : ℝ≥0)
    (h : Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct)) :
    joint (IBMSceneryClockIto.jointIntegral T h) = IBMSceneryNativeAdjoint.field T h := by
  change scalar.compLpL 2 gaussianProduct
    (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
      (IBMSceneryClockIto.jointIntegral T h)) = _
  rw [IBMSceneryClockIto.joint_curry]
  change scalar.compLpL 2 gaussianProduct _ =
    BochnerLinearIsometry.lift gaussianProduct (IBMSceneryNativeAdjoint.nativeField T)
      (IBMSceneryClockIto.inputSections T h)
  apply Lp.ext
  filter_upwards [scalar.coeFn_compLpL
    (BochnerLinearIsometry.lift gaussianProduct (GaussianComplexHorizonIto.realIto T)
      (IBMSceneryClockIto.inputSections T h)),
    BochnerLinearIsometry.lift_coeFn gaussianProduct (GaussianComplexHorizonIto.realIto T)
      (IBMSceneryClockIto.inputSections T h),
    BochnerLinearIsometry.lift_coeFn gaussianProduct (IBMSceneryNativeAdjoint.nativeField T)
      (IBMSceneryClockIto.inputSections T h)] with X hs hi hf
  rw [hs,hi,hf]
  exact scalar_native T _

theorem heat_native (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    joint (IBMSchwartzHeatPredictable.value g a T) =
      IBMSchwartzHeatPredictable.nativeField g a T :=
  joint_native T _

end OperatorDerivativeRewrite.Foundation.IBMNativeClockRecovery
