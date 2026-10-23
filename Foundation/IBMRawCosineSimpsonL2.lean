import Foundation.IBMSimpsonL2Error
import Foundation.IBMSimpsonGraphDual

/-! The original UNCLIPPED cosine Simpson sums converge strongly in observable
L2. Their full joint graph-dual limit still has no strong field representative. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawCosineSimpsonL2
open IBMSourceLaws IBMConstructedSources IBMActualSimpson IBMTimeAveragedObservable
open IBMActualSineDomainObstruction IBMJointIntrinsicDerivative
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local irreducible] ibmValue clockPath sceneryPath

theorem sine_fifth_bound (z : ℝ) : ‖iteratedDeriv 5 Real.sin z‖ ≤ (1 : ℝ) :=
  Real.abs_iteratedDeriv_sin_le_one 5 z

def valueClass (T : ℝ≥0) (n : ℕ) : JointL2 :=
  IBMSimpsonL2Error.errorClass Real.sin (by fun_prop) 1 sine_fifth_bound T n +
    (sinePoint T : JointL2)

theorem valueClass_actual_ae (T : ℝ≥0) (n : ℕ) :
    valueClass T n =ᵐ[jointMeasure] sums Real.cos T n := by
  filter_upwards [IBMSimpsonL2Error.errorClass_actual_ae Real.sin (by fun_prop) 1
    sine_fifth_bound T n, sinePoint_actual_ae T, IBMSimpsonGraphDual.sine_zero_ae,
    Lp.coeFn_add (IBMSimpsonL2Error.errorClass Real.sin (by fun_prop) 1
      sine_fifth_bound T n) (sinePoint T : JointL2)] with ω he hs hz ha
  change (IBMSimpsonL2Error.errorClass Real.sin (by fun_prop) 1
    sine_fifth_bound T n + (sinePoint T : JointL2)) ω = _
  rw [ha]
  simp only [Pi.add_apply]
  rw [he, hs]
  simp only [error, Real.deriv_sin, hz, sub_zero, sub_add_cancel]

theorem sums_memLp (T : ℝ≥0) (n : ℕ) : MemLp (sums Real.cos T n) 2 jointMeasure :=
  (memLp_congr_ae (valueClass_actual_ae T n)).mp (Lp.memLp (valueClass T n))

theorem sums_observable (T : ℝ≥0) (n : ℕ) :
    Measurable[IBMConditionalObservable.observableSigma sceneryPath clockPath]
      (sums Real.cos T n) := by
  have hm (r : ℝ≥0) : Measurable[
      IBMConditionalObservable.observableSigma sceneryPath clockPath] (ibmValue r) := by
    unfold IBMConditionalObservable.observableSigma IBMConstructedSources.ibmValue
    exact (measurable_pi_apply r).comp (comap_measurable
      (fun ω s => IBMContinuousComposition.value sceneryPath clockPath s ω))
  unfold sums IBMSimpsonPeano.simpson
  apply Finset.measurable_sum
  intro i hi
  exact (((hm _).sub (hm _)).div_const 6).mul
    (((Real.continuous_cos.measurable.comp (hm _)).add
      ((Real.continuous_cos.measurable.comp (((hm _).add (hm _)).div_const 2)).const_mul 4)).add
        (Real.continuous_cos.measurable.comp (hm _)))

def intrinsicValue (T : ℝ≥0) (n : ℕ) : IntrinsicSpace :=
  ⟨valueClass T n, ⟨sums Real.cos T n, (sums_observable T n).stronglyMeasurable,
    valueClass_actual_ae T n⟩⟩

theorem intrinsicValue_actual_ae (T : ℝ≥0) (n : ℕ) :
    (intrinsicValue T n : JointL2) =ᵐ[jointMeasure] sums Real.cos T n :=
  valueClass_actual_ae T n

/-- Every nonnegative horizon, including zero, on all uniform grids N=n+1. -/
theorem valueClass_tendsto (T : ℝ≥0) :
    Tendsto (valueClass T) atTop (𝓝 (sinePoint T : JointL2)) := by
  change Tendsto (fun n => IBMSimpsonL2Error.errorClass Real.sin (by fun_prop) 1
    sine_fifth_bound T n + (sinePoint T : JointL2)) atTop (𝓝 _)
  have h := (IBMSimpsonL2Error.errorClass_tendsto Real.sin (by fun_prop) 1
    sine_fifth_bound T).add_const (sinePoint T : JointL2)
  rw [zero_add] at h
  exact h

theorem intrinsicValue_tendsto (T : ℝ≥0) :
    Tendsto (intrinsicValue T) atTop (𝓝 (sinePoint T)) :=
  tendsto_subtype_rng.mpr (valueClass_tendsto T)

theorem weakDerivative_tendsto (T : ℝ≥0) :
    Tendsto (fun n => IBMIntrinsicGraphDual.weakDerivative (intrinsicValue T n)) atTop
      (𝓝 (sineDerivative T)) :=
  (IBMIntrinsicGraphDual.weakDerivative.continuous.tendsto _).comp (intrinsicValue_tendsto T)

attribute [local irreducible] intrinsicValue valueClass

theorem actual_pairing_integrable (T : ℝ≥0) (n : ℕ) (v : jointDivergence.domain) :
    Integrable (fun ω => sums Real.cos T n ω *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω) jointMeasure :=
  IBMIntrinsicGraphDual.actual_pairing_integrable (intrinsicValue T n) (sums Real.cos T n)
    (intrinsicValue_actual_ae T n) v

theorem actual_pairing_tendsto (T : ℝ≥0) (v : jointDivergence.domain) :
    Tendsto (fun n => ∫ ω, sums Real.cos T n ω *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω ∂jointMeasure) atTop
      (𝓝 (sineDerivative T (IBMIntrinsicGraphDual.testOf v))) := by
  have he : (fun n => ∫ ω, sums Real.cos T n ω *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω ∂jointMeasure) =
      fun n => IBMIntrinsicGraphDual.weakDerivative (intrinsicValue T n)
        (IBMIntrinsicGraphDual.testOf v) := by
    funext n
    exact (IBMIntrinsicGraphDual.actual_pairing (intrinsicValue T n) (sums Real.cos T n)
      (intrinsicValue_actual_ae T n) v).symm
  have hp := ((ContinuousLinearMap.apply ℝ ℝ (IBMIntrinsicGraphDual.testOf v)).continuous.tendsto
    (sineDerivative T)).comp (weakDerivative_tendsto T)
  exact hp.congr' (Eventually.of_forall fun n => (congrFun he n).symm)

end OperatorDerivativeRewrite.Foundation.IBMRawCosineSimpsonL2
