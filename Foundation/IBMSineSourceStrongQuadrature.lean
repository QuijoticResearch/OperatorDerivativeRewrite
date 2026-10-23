import Foundation.IBMSineSourceContinuity

/-! Genuine strong source-graph and native source-field quadrature limits
for the actual nonlinear IBM time average. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineSourceStrongQuadrature
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open IBMJointIntrinsicDerivative IBMActualSineDomainObstruction IBMClockOverlapEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem gradient_continuous : Continuous (fun t : ℝ => sineSourceGradient t.toNNReal) := by
  have he (t : ℝ) : sineSourceGradient t.toNNReal =
      ProductL2Curry.curryEquiv gaussianProduct gaussianProduct (IBMSineSourceField.flat t) := by
    rw [IBMSineSourceField.flat_eq]
    exact ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).apply_symm_apply _).symm
  simp_rw [he]
  exact (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).continuous.comp
    IBMSineSourceContinuity.flat_continuous

theorem nativeField_continuous : Continuous IBMSineSourceIntegral.nativeField :=
  IBMClockVectorTranspose.swap.continuous.comp IBMSineSourceContinuity.flat_continuous

theorem gradientSum_tendsto (T : ℝ≥0) :
    Tendsto (IBMSineAverageSourceDomain.gradientSum T) atTop
      (𝓝 (IBMSineAverageIntrinsicCalculus.gradient T 0)) := by
  have h := IBMBochnerTimeQuadrature.rightSum_tendsto
    (fun t : ℝ => sineSourceGradient t.toNNReal) gradient_continuous T.property
  have he : (∫ t in (0 : ℝ)..(T : ℝ), sineSourceGradient t.toNNReal) =
      IBMSineAverageIntrinsicCalculus.gradient T 0 := by
    calc
      _ = IBMSineSourceIntegral.sourceIntegral T := intervalIntegral.integral_of_le T.property
      _ = _ := IBMSineSourceIntegral.sourceIntegral_eq_gradient T
  exact he ▸ h

theorem source_graph_tendsto (T : ℝ≥0) :
    Tendsto (fun n =>
      (IBMBochnerTimeQuadrature.rightSum IBMSineAverageSourceDomain.valueCurve T (n + 1),
        IBMSineAverageSourceDomain.gradientSum T n)) atTop
      (𝓝 (sourceUnitary (IBMSineAverageSimpson.average T : JointL2),
        IBMSineAverageIntrinsicCalculus.gradient T 0)) :=
  (IBMSineAverageWeakGradient.source_value_tendsto T).prodMk_nhds (gradientSum_tendsto T)

def nativeSum (T : ℝ≥0) (n : ℕ) : IBMIntrinsicChainRule.JointVectorL2 :=
  IBMBochnerTimeQuadrature.rightSum IBMSineSourceIntegral.nativeField T (n + 1)

theorem nativeSum_tendsto (T : ℝ≥0) :
    Tendsto (nativeSum T) atTop
      (𝓝 (IBMClockVectorTranspose.realize (IBMSineAverageIntrinsicCalculus.gradient T 0))) := by
  have h := IBMBochnerTimeQuadrature.rightSum_tendsto
    IBMSineSourceIntegral.nativeField nativeField_continuous T.property
  have he : (∫ t in (0 : ℝ)..(T : ℝ), IBMSineSourceIntegral.nativeField t) =
      IBMClockVectorTranspose.realize (IBMSineAverageIntrinsicCalculus.gradient T 0) := by
    calc
      _ = ∫ t, IBMSineSourceIntegral.nativeField t ∂window T :=
        intervalIntegral.integral_of_le T.property
      _ = _ := (IBMSineSourceIntegral.native_source_formula T).symm
  exact he ▸ h

theorem nativeSum_norm_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ‖nativeSum T n‖) atTop
      (𝓝 ‖IBMSineAverageIntrinsicCalculus.gradient T 0‖) := by
  have h := (nativeSum_tendsto T).norm
  have he : ‖IBMClockVectorTranspose.realize (IBMSineAverageIntrinsicCalculus.gradient T 0)‖ =
      ‖IBMSineAverageIntrinsicCalculus.gradient T 0‖ := IBMClockVectorTranspose.realize.norm_map _
  exact he ▸ h

end OperatorDerivativeRewrite.Foundation.IBMSineSourceStrongQuadrature
