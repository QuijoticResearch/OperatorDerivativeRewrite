import Foundation.IBMNonlinearClockGraph

/-! Actual closed-clock derivatives of mollified sine time averages.
The energy bound now controls graph outputs, not merely candidate fields. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearClockAverageGraph
open InfiniteGaussian IBMTimeAveragedObservable IBMClockOverlapEnergy
open IBMIntrinsicOperators IBMNonlinearClockGraph
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def sineValue (n : ℕ) (t : ℝ) : JointL2 :=
  IBMClockWeakChain.value IBMActualSineDomainObstruction.sineTest (input n t.toNNReal)

theorem sineValue_continuous (n : ℕ) : Continuous (sineValue n) :=
  (IBMClockWeakChain.value_L2_lipschitz IBMActualSineDomainObstruction.sineTest).continuous.comp
    (jointRealization.continuous.comp
      ((mollified_time_continuous n).comp continuous_real_toNNReal))

theorem sineValue_norm_le (n : ℕ) (t : ℝ) : ‖sineValue n t‖ ≤ 1 := by
  have ha : ∀ᵐ p ∂IBMSourceLaws.jointMeasure, ‖sineValue n t p‖ ≤ (1 : ℝ) := by
    filter_upwards [IBMClockWeakChain.value_ae IBMActualSineDomainObstruction.sineTest
      (input n t.toNNReal)] with p hp
    change ‖IBMClockWeakChain.value IBMActualSineDomainObstruction.sineTest (input n t.toNNReal) p‖ ≤ 1
    rw [hp]
    exact Real.abs_sin_le_one _
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (f := sineValue n t) zero_le_one ha

theorem sineValue_integrable (n : ℕ) (T : ℝ) : Integrable (sineValue n) (window T) :=
  Integrable.of_bound (sineValue_continuous n).aestronglyMeasurable 1
    (ae_of_all _ (sineValue_norm_le n))

def average (n : ℕ) (T : ℝ) : JointL2 := ∫ t, sineValue n t ∂window T

def averageGradient (n : ℕ) (T : ℝ) : FieldSpace :=
  IBMClockVectorTranspose.clockField (IBMNonlinearClockEnergy.average n T)

theorem gradient_integrable (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun t => IBMClockVectorTranspose.clockField (IBMNonlinearClockField.field n t))
      (window T) :=
  IBMClockVectorTranspose.clockField.toContinuousLinearMap.integrable_comp
    (IBMNonlinearClockField.field_integrable n hT)

theorem integral_clock_graph {μ : Measure ℝ} (u : ℝ → ScalarFieldSpace) (v : ℝ → FieldSpace)
    (hu : Integrable u μ) (hv : Integrable v μ)
    (ha : ∀ᵐ t ∂μ, (u t, v t) ∈ IBMClockGraphDualLimit.Clock.graph) :
    (∫ t, u t ∂μ, ∫ t, v t ∂μ) ∈ IBMClockGraphDualLimit.Clock.graph := by
  let S := IBMClockGraphDualLimit.Clock.graph
  letI : IsClosed (S : Set (ScalarFieldSpace × FieldSpace)) := IBMClockGraphDualLimit.clock_closed
  let f : ℝ → ScalarFieldSpace × FieldSpace := fun t => (u t, v t)
  have hf : Integrable f μ := hu.prodMk hv
  have hq : S.mkQL (∫ t, f t ∂μ) = 0 := by
    rw [← S.mkQL.integral_comp_comm hf]
    apply integral_eq_zero_of_ae
    filter_upwards [ha] with t ht
    exact (Submodule.Quotient.mk_eq_zero S).mpr ht
  have hm := (Submodule.Quotient.mk_eq_zero S).mp hq
  rwa [show (∫ t, f t ∂μ) = (∫ t, u t ∂μ, ∫ t, v t ∂μ) from integral_pair hu hv] at hm

attribute [local irreducible] sineValue IBMNonlinearClockField.field
  IBMClockVectorTranspose.clockField

theorem average_clock_graph (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (clockUnitary (average n T), averageGradient n T) ∈ IBMClockGraphDualLimit.Clock.graph := by
  have hu : Integrable (fun t => clockUnitary (sineValue n t)) (window T) :=
    clockUnitary.toLinearIsometry.toContinuousLinearMap.integrable_comp (sineValue_integrable n T)
  have hv := gradient_integrable n hT
  have ha : ∀ᵐ t ∂window T, (clockUnitary (sineValue n t),
      IBMClockVectorTranspose.clockField (IBMNonlinearClockField.field n t)) ∈
        IBMClockGraphDualLimit.Clock.graph := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h := sine_clock_graph n t.toNNReal (Real.toNNReal_pos.mpr ht.1)
    rw [Real.coe_toNNReal _ ht.1.le] at h
    simpa only [sineValue] using h
  have hm := integral_clock_graph _ _ hu hv ha
  have he : (∫ t, clockUnitary (sineValue n t) ∂window T) = clockUnitary (average n T) :=
    clockUnitary.toLinearIsometry.toContinuousLinearMap.integral_comp_comm (sineValue_integrable n T)
  rw [he,
    ← IBMClockVectorTranspose.clockField_integral _ (IBMNonlinearClockField.field_integrable n hT)] at hm
  exact hm

theorem averageGradient_uniform_energy (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖averageGradient n T‖ ^ 2 ≤
      8 * IBMFoldedTransitionBound.peak 1 * T ^ 2 * Real.sqrt T + 4 * T ^ 3 := by
  rw [averageGradient, IBMClockVectorTranspose.clockField_norm]
  exact IBMNonlinearClockEnergy.average_uniform_energy n hT

theorem averageGradient_norm_bound (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖averageGradient n T‖ ≤
      Real.sqrt (8 * IBMFoldedTransitionBound.peak 1 * T ^ 2 * Real.sqrt T + 4 * T ^ 3) := by
  rw [averageGradient, IBMClockVectorTranspose.clockField_norm]
  exact IBMNonlinearClockEnergy.average_norm_bound n hT

end OperatorDerivativeRewrite.Foundation.IBMNonlinearClockAverageGraph
