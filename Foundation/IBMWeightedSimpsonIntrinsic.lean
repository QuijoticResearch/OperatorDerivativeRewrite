import Foundation.IBMWeightedSimpsonL2Realization
import Foundation.IBMIntrinsicGraphDual

/-! Actual time-weighted spatial stochastic integrals in the original
observable L2 and full joint adjoint graph dual. No strong domain is inferred. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMWeightedSimpsonIntrinsic
open IBMSourceLaws IBMConstructedSources IBMTimeWeightedSimpson IBMTimeAveragedObservable
open IBMJointIntrinsicDerivative IBMWeightedSimpsonL2Realization IBMUniformClockGridEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local irreducible] ibmValue clockPath sceneryPath

theorem weighted_observable (h g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) (n : ℕ) :
    Measurable[IBMConditionalObservable.observableSigma sceneryPath clockPath]
      (weighted h g T n) := by
  have hm (r : ℝ≥0) : Measurable[
      IBMConditionalObservable.observableSigma sceneryPath clockPath] (ibmValue r) := by
    unfold IBMConditionalObservable.observableSigma IBMConstructedSources.ibmValue
    exact (measurable_pi_apply r).comp (comap_measurable
      (fun ω s => IBMContinuousComposition.value sceneryPath clockPath s ω))
  have hc : Continuous (fun p : ℝ × ℝ => IBMSimpsonPeano.simpson g p.1 p.2) := by
    unfold IBMSimpsonPeano.simpson
    fun_prop
  unfold weighted
  apply Finset.measurable_sum
  intro i hi
  exact (hc.measurable.comp
    ((hm (grid (T/(n+1)) i)).prodMk (hm (grid (T/(n+1)) (i+1))))).const_mul _

variable (h f : ℝ → ℝ) (hh : ContDiff ℝ 1 h) (hf : ContDiff ℝ 5 f)
  (F M : ℝ) (hF : ∀ z, |f z| ≤ F) (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M)

theorem valueClass_intrinsic (T : ℝ≥0) (n : ℕ) :
    valueClass h f hh hf F M hF hM T n ∈ IntrinsicSpace :=
  ⟨weighted h (deriv f) T n,
    (weighted_observable h (deriv f) (hf.continuous_deriv (by norm_num)) T n).stronglyMeasurable,
    valueClass_actual_ae h f hh hf F M hF hM T n⟩

def intrinsicValue (T : ℝ≥0) (n : ℕ) : IntrinsicSpace :=
  ⟨valueClass h f hh hf F M hF hM T n, valueClass_intrinsic h f hh hf F M hF hM T n⟩

include M hM in
theorem targetClass_intrinsic (T : ℝ≥0) : targetClass h f hh hf F hF T ∈ IntrinsicSpace := by
  have hc : IsClosed (IntrinsicSpace : Set JointL2) :=
    IBMConditionalObservable.observableSpace_isClosed _ _
      sceneryPath_measurable clockPath_measurable
  exact hc.mem_of_tendsto (valueClass_tendsto h f hh hf F M hF hM T)
    (Eventually.of_forall (valueClass_intrinsic h f hh hf F M hF hM T))

def intrinsicTarget (T : ℝ≥0) : IntrinsicSpace :=
  ⟨targetClass h f hh hf F hF T, targetClass_intrinsic h f hh hf F M hF hM T⟩

theorem intrinsicValue_actual_ae (T : ℝ≥0) (n : ℕ) :
    (intrinsicValue h f hh hf F M hF hM T n : JointL2) =ᵐ[jointMeasure]
      weighted h (deriv f) T n := valueClass_actual_ae h f hh hf F M hF hM T n

/-- The limit is the ACTUAL time-space chain expression on the original paths. -/
theorem intrinsicTarget_actual_ae (T : ℝ≥0) :
    (intrinsicTarget h f hh hf F M hF hM T : JointL2) =ᵐ[jointMeasure]
      (fun ω => h T*f (ibmValue T ω)-h 0*f (ibmValue 0 ω)-
        ∫ t in (0 : ℝ)..(T : ℝ), deriv h t*f (ibmValue (Real.toNNReal t) ω)) :=
  (targetClass_actual_ae h f hh hf F hF T).trans
    (ae_of_all _ (derivative_target_identity h f hh (hf.of_le (by norm_num)) T))

theorem intrinsicValue_tendsto (T : ℝ≥0) :
    Tendsto (intrinsicValue h f hh hf F M hF hM T) atTop
      (𝓝 (intrinsicTarget h f hh hf F M hF hM T)) :=
  tendsto_subtype_rng.mpr (valueClass_tendsto h f hh hf F M hF hM T)

theorem weakDerivative_tendsto (T : ℝ≥0) :
    Tendsto (fun n => IBMIntrinsicGraphDual.weakDerivative (intrinsicValue h f hh hf F M hF hM T n))
      atTop (𝓝 (IBMIntrinsicGraphDual.weakDerivative (intrinsicTarget h f hh hf F M hF hM T))) :=
  (IBMIntrinsicGraphDual.weakDerivative.continuous.tendsto _).comp
    (intrinsicValue_tendsto h f hh hf F M hF hM T)

attribute [local irreducible] intrinsicValue intrinsicTarget jointDerivative
  IBMWeightedSimpsonL2Realization.valueClass IBMWeightedSimpsonL2Realization.targetClass
  IBMIntrinsicGraphDual.weakDerivative IBMIntrinsicGraphDual.testOf

include hh hf F M hF hM in
theorem actual_pairing_integrable (T : ℝ≥0) (n : ℕ) (v : jointDivergence.domain) :
    Integrable (fun ω => weighted h (deriv f) T n ω *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω) jointMeasure :=
  IBMIntrinsicGraphDual.actual_pairing_integrable (intrinsicValue h f hh hf F M hF hM T n)
    (weighted h (deriv f) T n) (intrinsicValue_actual_ae h f hh hf F M hF hM T n) v

include hh hf F M hF hM in
/-- The limiting product with every original adjoint test is integrable. -/
theorem target_pairing_integrable (T : ℝ≥0) (v : jointDivergence.domain) :
    Integrable (fun ω => (h T*f (ibmValue T ω)-h 0*f (ibmValue 0 ω)-
      ∫ t in (0 : ℝ)..(T : ℝ), deriv h t*f (ibmValue (Real.toNNReal t) ω)) *
        ((jointDivergence v : IntrinsicSpace) : JointL2) ω) jointMeasure :=
  IBMIntrinsicGraphDual.actual_pairing_integrable (intrinsicTarget h f hh hf F M hF hM T)
    _ (intrinsicTarget_actual_ae h f hh hf F M hF hM T) v

include hh hf F M hF hM in
/-- Actual finite-sum pairings converge against every original adjoint test. -/
theorem dual_pairing_tendsto (T : ℝ≥0) (v : jointDivergence.domain) :
    Tendsto (fun n => ∫ ω, weighted h (deriv f) T n ω *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω ∂jointMeasure) atTop
      (𝓝 (IBMIntrinsicGraphDual.weakDerivative (intrinsicTarget h f hh hf F M hF hM T)
        (IBMIntrinsicGraphDual.testOf v))) := by
  have hp := ((ContinuousLinearMap.apply ℝ ℝ (IBMIntrinsicGraphDual.testOf v)).continuous.tendsto
    (IBMIntrinsicGraphDual.weakDerivative (intrinsicTarget h f hh hf F M hF hM T))).comp
      (weakDerivative_tendsto h f hh hf F M hF hM T)
  have he (n : ℕ) := IBMIntrinsicGraphDual.actual_pairing
    (intrinsicValue h f hh hf F M hF hM T n) (weighted h (deriv f) T n)
      (intrinsicValue_actual_ae h f hh hf F M hF hM T n) v
  exact hp.congr' (Eventually.of_forall he)

/-- The graph-dual limit has the explicit original-path time correction. -/
theorem target_actual_pairing (T : ℝ≥0) (v : jointDivergence.domain) :
    IBMIntrinsicGraphDual.weakDerivative (intrinsicTarget h f hh hf F M hF hM T)
      (IBMIntrinsicGraphDual.testOf v) =
        ∫ ω, (h T*f (ibmValue T ω)-h 0*f (ibmValue 0 ω)-
          ∫ t in (0 : ℝ)..(T : ℝ), deriv h t*f (ibmValue (Real.toNNReal t) ω)) *
            ((jointDivergence v : IntrinsicSpace) : JointL2) ω ∂jointMeasure :=
  IBMIntrinsicGraphDual.actual_pairing (intrinsicTarget h f hh hf F M hF hM T)
    _ (intrinsicTarget_actual_ae h f hh hf F M hF hM T) v

include hh hf F M hF hM in
/-- Actual original adjoint-domain pairing convergence, including the explicit
Lebesgue time correction in the stochastic limit. -/
theorem actual_pairing_tendsto (T : ℝ≥0) (v : jointDivergence.domain) :
    Tendsto (fun n => ∫ ω, weighted h (deriv f) T n ω *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω ∂jointMeasure) atTop
      (𝓝 (∫ ω, (h T*f (ibmValue T ω)-h 0*f (ibmValue 0 ω)-
        ∫ t in (0 : ℝ)..(T : ℝ), deriv h t*f (ibmValue (Real.toNNReal t) ω)) *
          ((jointDivergence v : IntrinsicSpace) : JointL2) ω ∂jointMeasure)) := by
  have hp := dual_pairing_tendsto h f hh hf F M hF hM T v
  rw [target_actual_pairing h f hh hf F M hF hM T v] at hp
  exact hp

end OperatorDerivativeRewrite.Foundation.IBMWeightedSimpsonIntrinsic
