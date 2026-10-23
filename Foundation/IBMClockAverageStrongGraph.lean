import Foundation.BochnerCoefficientParseval
import Foundation.IBMClockOccupationStrong
import Foundation.IBMIntrinsicChainRule

/-! Strong convergence of the full ORIGINAL clock gradients of actual linear
IBM time averages. Parseval sums the verified directional energy domination;
the original closed-graph weak limit then gives the full vector norm limit. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockAverageStrongGraph
open InfiniteGaussian IBMFirstSourceClockGraph IBMClockAverageGraph
open IBMClockPhysicalOccupation
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem directional_norm_sq_le (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    ‖directional h (averageGradient n T)‖ ^ 2 ≤ ‖directional h (gradient T)‖ ^ 2 := by
  calc
    _ = ‖kernelApprox h n T‖ ^ 2 := by rw [← kernelApprox_realization, noiseLift.norm_map]
    _ ≤ ‖kernel h T‖ ^ 2 := IBMClockOccupationStrong.kernel_norm_sq_le h n T
    _ = _ := by rw [← kernel_realization, noiseLift.norm_map]

theorem gradient_norm_sq_le (n : ℕ) (T : ℝ≥0) : ‖averageGradient n T‖ ^ 2 ≤ ‖gradient T‖ ^ 2 :=
  BochnerCoefficientParseval.norm_sq_le_of_directional _ _
    (fun i => directional_norm_sq_le (BochnerCoefficientParseval.basis i) n T)

attribute [local irreducible] averageGradient gradient

theorem gradient_tendsto (T : ℝ≥0) :
    Tendsto (fun n => averageGradient n T) atTop (𝓝 (gradient T)) := by
  have hp := gradient_pairing_tendsto T (gradient T)
  have ht : Tendsto (fun n => 2 * ‖gradient T‖ ^ 2 -
      2 * inner ℝ (averageGradient n T) (gradient T)) atTop (𝓝 (0 : ℝ)) := by
    have hl := (tendsto_const_nhds (x := 2 * ‖gradient T‖ ^ 2)).sub (hp.const_mul 2)
    have he : 2 * ‖gradient T‖ ^ 2 - 2 * inner ℝ (gradient T) (gradient T) = 0 := by
      rw [real_inner_self_eq_norm_sq]
      ring
    exact he ▸ hl
  have hb (n : ℕ) : ‖averageGradient n T - gradient T‖ ^ 2 ≤
      2 * ‖gradient T‖ ^ 2 - 2 * inner ℝ (averageGradient n T) (gradient T) := by
    rw [norm_sub_sq_real]
    linarith [gradient_norm_sq_le n T]
  have hs := squeeze_zero (fun n => sq_nonneg ‖averageGradient n T - gradient T‖) hb ht
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have hn : Tendsto (fun n => ‖averageGradient n T - gradient T‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hr
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

theorem gradient_norm_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ‖averageGradient n T‖) atTop (𝓝 ‖gradient T‖) := (gradient_tendsto T).norm

theorem original_graph_tendsto (T : ℝ≥0) :
    Tendsto (fun n => (flip (IBMTimeAveragedObservable.mollifiedAverage n T), averageGradient n T))
      atTop (𝓝 (flip (IBMTimeAveragedObservable.sourceAverage T), gradient T)) :=
  (flip.continuous.continuousAt.tendsto.comp
    (IBMTimeAveragedObservable.average_tendsto T.property)).prodMk_nhds (gradient_tendsto T)

/-- Original source/clock order in the actual coefficient-valued joint L2.
No scalar directional contraction remains in this theorem. -/
theorem native_clock_field_tendsto (T : ℝ≥0) :
    Tendsto (fun n => IBMIntrinsicChainRule.uncurryField (averageGradient n T)) atTop
      (𝓝 (IBMIntrinsicChainRule.uncurryField (gradient T))) :=
  (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.continuous.continuousAt.tendsto.comp
    (gradient_tendsto T)

theorem native_clock_field_norm_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ‖IBMIntrinsicChainRule.uncurryField (averageGradient n T)‖) atTop
      (𝓝 ‖IBMIntrinsicChainRule.uncurryField (gradient T)‖) := (native_clock_field_tendsto T).norm

/-- The limit is the original intrinsic clock derivative of the ACTUAL
IBM-observable time average. No observability of mollified approximants is assumed. -/
theorem limit_intrinsic_clock_graph (T : ℝ≥0) :
    (IBMTimeAveragedObservable.intrinsicAverage T, gradient T) ∈
      IBMIntrinsicOperators.intrinsicClock.graph := by
  apply IBMIntrinsicChainRule.clock_intrinsic_graph
  have hu : IBMIntrinsicOperators.clockUnitary
      (IBMTimeAveragedObservable.intrinsicAverage T : IBMTimeAveragedObservable.JointL2) =
        flip (IBMTimeAveragedObservable.sourceAverage T) := by
    rw [← IBMTimeAveragedObservable.nativeAverage_eq_intrinsicAverage]
    exact nativeAverage_clock_representation T
  rw [hu]
  exact gradient_graph T

end OperatorDerivativeRewrite.Foundation.IBMClockAverageStrongGraph
