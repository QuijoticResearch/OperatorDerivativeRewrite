import Foundation.IBMNonlinearClockStrongLimit
import Foundation.IBMSineAverageWeakGradient

/-! Original native nonlinear clock gradients converge STRONGLY to the actual
intrinsic clock component of int_0^T sin(Z_t) dt. The existing graph/domain and
weak-limit identifications are reused, not assumed for arbitrary observables. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineAverageStrongClock
open InfiniteGaussian IBMNonlinearClockStrongLimit IBMClockVectorTranspose
open IBMIntrinsicOperators IBMJointIntrinsicDerivative IBMSineAverageIntrinsicCalculus
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem nativeLimit_clock_eq (T : ℝ≥0) :
    clockField (nativeLimit T) = gradient T 1 := by
  apply ext_inner_right ℝ
  intro w
  have ht := clockField.continuous.continuousAt.tendsto.comp (native_tendsto T)
  have hi : Tendsto (fun n => inner ℝ
      (clockField (IBMNonlinearClockEnergy.average n T)) w) atTop
        (𝓝 (inner ℝ (clockField (nativeLimit T)) w)) :=
    ht.inner (tendsto_const_nhds (x := w))
  have hw := IBMSineAverageWeakGradient.clock_pairing_tendsto T w
  exact tendsto_nhds_unique hi hw

theorem clockGradient_tendsto (T : ℝ≥0) :
    Tendsto (fun n => IBMNonlinearClockAverageGraph.averageGradient n T) atTop
      (𝓝 (gradient T 1)) := by
  have ht := clockField.continuous.continuousAt.tendsto.comp (native_tendsto T)
  rw [nativeLimit_clock_eq] at ht
  exact ht

theorem original_clock_graph_tendsto (T : ℝ≥0) :
    Tendsto (fun n =>
      (clockUnitary (IBMNonlinearClockAverageGraph.average n T),
        IBMNonlinearClockAverageGraph.averageGradient n T)) atTop
      (𝓝 (clockUnitary (IBMSineAverageSimpson.average T : IBMTimeAveragedObservable.JointL2),
        gradient T 1)) :=
  (IBMSineAverageWeakGradient.clock_value_tendsto T).prodMk_nhds (clockGradient_tendsto T)

theorem limit_clock_graph (T : ℝ≥0) :
    (clockUnitary (IBMSineAverageSimpson.average T : IBMTimeAveragedObservable.JointL2),
      clockField (nativeLimit T)) ∈ IBMClockGraphDualLimit.Clock.graph := by
  rw [nativeLimit_clock_eq]
  exact IBMSineAverageWeakGradient.clock_graph T

/-- The source/clock-order joint coefficient-valued L2 fields themselves
converge, with no remaining scalar probe or finite coefficient truncation. -/
theorem native_joint_clock_tendsto (T : ℝ≥0) :
    Tendsto (fun n => IBMIntrinsicChainRule.uncurryField
      (IBMNonlinearClockAverageGraph.averageGradient n T)) atTop
        (𝓝 (IBMIntrinsicChainRule.uncurryField (gradient T 1))) := by
  have hc := (ProductL2Curry.curryEquiv (E := CoefficientSpace)
    gaussianProduct gaussianProduct).symm.continuous
  exact hc.continuousAt.tendsto.comp (clockGradient_tendsto T)

theorem clockGradient_norm_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ‖IBMNonlinearClockAverageGraph.averageGradient n T‖) atTop
      (𝓝 ‖gradient T 1‖) := (clockGradient_tendsto T).norm

end OperatorDerivativeRewrite.Foundation.IBMSineAverageStrongClock
