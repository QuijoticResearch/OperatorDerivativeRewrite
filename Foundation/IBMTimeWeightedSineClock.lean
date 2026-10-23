import Foundation.IBMTimeWeightedSineValue

/-! Actual rough-time-weighted sine functionals belong to the original closed
clock domain. Native clock gradients have uniform energy, not an assumed limit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTimeWeightedSineClock
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMClockOverlapEnergy
open IBMNonlinearClockAverageGraph IBMTimeWeightedSineValue IBMClockVectorTranspose
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def nativeGradient (n : ℕ) (g : ℝ → ℝ) (T : ℝ≥0) : FieldSpace :=
  clockField (∫ t, g t • IBMNonlinearClockField.field n t ∂window T)

def energy (g : ℝ → ℝ) (T : ℝ≥0) : ℝ :=
  (8*IBMFoldedTransitionBound.peak 1*(T:ℝ)*Real.sqrt T+4*(T:ℝ)^2)*
    (∫ t, (g t)^2 ∂window T)

theorem native_energy (n : ℕ) (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    ‖nativeGradient n g T‖^2 ≤ energy g T := by
  rw [nativeGradient,clockField_norm]
  exact IBMClockTimeWeightEnergy.weighted_energy n g T.property hg

theorem native_norm_bound (n : ℕ) (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    ‖nativeGradient n g T‖ ≤ Real.sqrt (energy g T) := by
  have hb := native_energy n g T hg
  have hB : 0 ≤ energy g T := (sq_nonneg ‖nativeGradient n g T‖).trans hb
  nlinarith [Real.sq_sqrt hB,Real.sqrt_nonneg (energy g T),norm_nonneg (nativeGradient n g T)]

theorem mollified_clock_graph (n : ℕ) (g : ℝ → ℝ) (T : ℝ≥0)
    (hg : MemLp g 2 (window T)) :
    (clockUnitary (mollified n g T),nativeGradient n g T) ∈ IBMClockGraphDualLimit.Clock.graph := by
  let u : ℝ → ScalarFieldSpace := fun t => g t • clockUnitary (sineValue n t)
  let v : ℝ → FieldSpace := fun t => clockField (g t • IBMNonlinearClockField.field n t)
  have hu : Integrable u (window T) := by
    simpa only [u,Function.comp_def,map_smul,
      LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry] using
      clockUnitary.toLinearIsometry.toContinuousLinearMap.integrable_comp
        (mollified_integrable n g T hg)
  have hv : Integrable v (window T) := by
    exact clockField.toContinuousLinearMap.integrable_comp
      (IBMClockTimeWeightEnergy.weighted_integrable n g T.property hg)
  have ha : ∀ᵐ t ∂window T, (u t,v t) ∈ IBMClockGraphDualLimit.Clock.graph := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hp := IBMNonlinearClockGraph.sine_clock_graph n t.toNNReal
      (Real.toNNReal_pos.mpr ht.1)
    rw [Real.coe_toNNReal _ ht.1.le] at hp
    have hf : (clockUnitary (sineValue n t),clockField (IBMNonlinearClockField.field n t)) ∈
        IBMClockGraphDualLimit.Clock.graph := by simpa only [sineValue] using hp
    simpa only [u,v,map_smul,Prod.smul_mk] using
      IBMClockGraphDualLimit.Clock.graph.smul_mem (g t) hf
  have hm := integral_clock_graph u v hu hv ha
  have hU : (∫ t, u t ∂window T) = clockUnitary (mollified n g T) := by
    simpa only [u,mollified,Function.comp_def,map_smul,
      LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry] using
      clockUnitary.toLinearIsometry.toContinuousLinearMap.integral_comp_comm
        (mollified_integrable n g T hg)
  have hV : (∫ t, v t ∂window T) = nativeGradient n g T := by
    exact clockField.toContinuousLinearMap.integral_comp_comm
      (IBMClockTimeWeightEnergy.weighted_integrable n g T.property hg)
  exact (congrArg (fun p : ScalarFieldSpace × FieldSpace =>
    p ∈ IBMClockGraphDualLimit.Clock.graph) (Prod.ext hU hV)).mp hm

theorem actual_clock_domain (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    clockUnitary (actual g T : JointL2) ∈ IBMClockGraphDualLimit.Clock.domain := by
  apply ClosedOperatorEscapeEnergy.mem_domain_of_frequently_bounded_graph
    IBMClockGraphDualLimit.Clock IBMClockGraphDualLimit.clock_closed
      IBMClockGraphDualLimit.clock_dense (fun n => mollified_clock_graph n g T hg)
        (clockUnitary.continuous.continuousAt.tendsto.comp (mollified_tendsto g T hg))
          (Real.sqrt (energy g T))
  exact (Eventually.of_forall fun n => native_norm_bound n g T hg).frequently

end OperatorDerivativeRewrite.Foundation.IBMTimeWeightedSineClock
