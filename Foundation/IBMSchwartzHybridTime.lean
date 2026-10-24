import Foundation.IBMNativeClockRecovery
import Foundation.IBMSchwartzHybridReconstruction
import Foundation.IBMSchwartzSimpsonNative
import Foundation.IBMClockWeakChain

/-! Horizon continuity of the SAME explicit native heat/source reconstruction.
In particular its physical-time Bochner integrals require no measurability
or integrable-field hypotheses to be supplied by the caller. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzHybridTime
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open IBMJointIntrinsicDerivative IBMSchwartzHybridReconstruction IBMSchwartzHeatDerivative
open IBMCorrectionStein IBMClockOverlapEnergy
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local irreducible] heatMean IBMSchwartzHalfHolderHeat.curve
  GaussianHalfHolderScore.score GaussianBoundedHeatDerivative.mean
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

def test (g : SchwartzMap ℝ ℝ) (a : ℝ) : IBMClockWeakChain.TestFunction where
  value := shiftedJet g a 0
  slope := shiftedJet g a 1
  valueBound := SchwartzMap.seminorm ℝ 0 0 (jet g 0)
  slopeBound := SchwartzMap.seminorm ℝ 0 0 (jet g 1)
  hasDeriv := fun x => by
    have h := ((shiftedJet_smooth g a 0).differentiable (by norm_num)).differentiableAt.hasDerivAt
      (x := x)
    rw [shiftedJet_deriv] at h
    exact h
  continuous_slope := (shiftedJet_smooth g a 1).continuous
  value_le := shiftedJet_bound g a 0
  slope_le := shiftedJet_bound g a 1

theorem terminal_eq (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    terminal g a T = IBMClockWeakChain.value (test g a) (intrinsicCurve T) := by
  apply Lp.ext
  filter_upwards [terminal_actual g a T,IBMClockWeakChain.value_ae (test g a)
    (intrinsicCurve T),joint_point_actual_ae T] with p ht hv hi
  change (intrinsicCurve T : JointL2) p = _ at hi
  rw [ht,hv,hi]
  rfl

theorem terminal_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    Continuous (terminal g a) := by
  have he : terminal g a = fun T => IBMClockWeakChain.value (test g a) (intrinsicCurve T) :=
    funext (terminal_eq g a)
  rw [he]
  exact (IBMClockWeakChain.value_L2_lipschitz (test g a)).continuous.comp
    (continuous_subtype_val.comp intrinsicCurve_continuous)

theorem initial_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    Continuous (fun T : ℝ≥0 => heatMean g a 0 T) :=
  (heatMean_continuous g a).comp (continuous_const.prodMk NNReal.continuous_coe)

theorem clock_value_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    Continuous (IBMSchwartzHeatPredictable.value g a) := by
  have he : IBMSchwartzHeatPredictable.value g a = fun T =>
      terminal g a T - jointRealization (Lp.const 2 gaussianProduct (heatMean g a 0 T)) := by
    funext T
    rw [IBMSchwartzHeatReconstruction.native_reconstruction,map_sub]
    rfl
  rw [he]
  exact (terminal_continuous g a).sub (jointRealization.continuous.comp
    ((Lp.constL 2 gaussianProduct ℝ).continuous.comp (initial_continuous g a)))

theorem clock_field_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    Continuous (IBMSchwartzHeatPredictable.nativeField g a) := by
  have he : IBMSchwartzHeatPredictable.nativeField g a =
      fun T => IBMNativeClockRecovery.joint (IBMSchwartzHeatPredictable.value g a T) :=
    funext fun T => (IBMNativeClockRecovery.heat_native g a T).symm
  rw [he]
  exact IBMNativeClockRecovery.joint.continuous.comp (clock_value_continuous g a)

theorem source_field_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    Continuous (sourceField g a) := by
  change Continuous (fun T : ℝ≥0 => BochnerClosedOperator.tensor gaussianProduct gaussianOne
    (GaussianDivergenceRecovery.recoveryOperator (heatMean g a 0 T)))
  exact (BochnerClosedOperator.tensor_continuous gaussianProduct gaussianOne).comp
    (GaussianDivergenceRecovery.recoveryOperator.continuous.comp (initial_continuous g a))

theorem mean_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) : Continuous (meanValue g a) := by
  change Continuous (fun T : ℝ≥0 => jointRealization (Lp.const 2 gaussianProduct
    (GaussianNumberSectors.projection 0 (heatMean g a 0 T))))
  exact jointRealization.continuous.comp ((Lp.constL 2 gaussianProduct ℝ).continuous.comp
    ((GaussianNumberSectors.projection 0).continuous.comp (initial_continuous g a)))

theorem centered_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    Continuous (centered g a) :=
  ((terminal_continuous g a).sub (mean_continuous g a)).subtype_mk _

theorem integrand_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    Continuous (integrand g a) := by
  change Continuous (fun T : ℝ≥0 =>
    pairField (sourceField g a T) (IBMSchwartzHeatPredictable.nativeField g a T))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => FieldSpace)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact source_field_continuous g a
  · exact clock_field_continuous g a

theorem centered_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Integrable (fun t : ℝ => centered g a t.toNNReal) (window T) :=
  ((centered_continuous g a).comp continuous_real_toNNReal).integrableOn_Icc.mono_set
    Ioc_subset_Icc_self

theorem integrand_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Integrable (fun t : ℝ => integrand g a t.toNNReal) (window T) :=
  ((integrand_continuous g a).comp continuous_real_toNNReal).integrableOn_Icc.mono_set
    Ioc_subset_Icc_self

end OperatorDerivativeRewrite.Foundation.IBMSchwartzHybridTime
