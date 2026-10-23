import Foundation.IBMSineAverageStrongClock
import Foundation.IBMSineSourceContinuity
import Foundation.IBMNativeBoundedGraphCore

/-! Strong convergence of both original native sine-average gradient channels,
and uniform actual divergence-test integration-by-parts errors. The native
pair is not asserted to share a single finite-stage graph input. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineAverageStrongJoint
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMSineAverageIntrinsicCalculus IBMActualSineDomainObstruction
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem sourceGradient_continuous : Continuous (fun t : ℝ => sineSourceGradient t.toNNReal) := by
  have he (t : ℝ) : sineSourceGradient t.toNNReal =
      ProductL2Curry.curryEquiv gaussianProduct gaussianProduct (IBMSineSourceField.flat t) := by
    rw [IBMSineSourceField.flat_eq]
    exact ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).apply_symm_apply _).symm
  simp_rw [he]
  exact (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).continuous.comp
    IBMSineSourceContinuity.flat_continuous

theorem sourceGradient_tendsto (T : ℝ≥0) :
    Tendsto (IBMSineAverageSourceDomain.gradientSum T) atTop (𝓝 (gradient T 0)) := by
  have ht := IBMBochnerTimeQuadrature.rightSum_tendsto
    (fun t : ℝ => sineSourceGradient t.toNNReal) sourceGradient_continuous T.property
  have hi : (∫ t in (0:ℝ)..(T:ℝ), sineSourceGradient t.toNNReal) = gradient T 0 :=
    (intervalIntegral.integral_of_le T.property).trans
      (IBMSineSourceIntegral.sourceIntegral_eq_gradient T)
  exact ht.mono_right (le_of_eq (congrArg (fun v : FieldSpace => 𝓝 v) hi))

/-- Ordinary full two-channel Hilbert norm, with every coefficient retained. -/
theorem nativePair_tendsto (T : ℝ≥0) :
    Tendsto (IBMSineAverageWeakGradient.nativePair T) atTop (𝓝 (gradient T)) := by
  apply IBMNativeBoundedGraphCore.field_limit
  intro i
  fin_cases i
  · exact sourceGradient_tendsto T
  · exact IBMSineAverageStrongClock.clockGradient_tendsto T

theorem nativePair_error_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ‖IBMSineAverageWeakGradient.nativePair T n - gradient T‖)
      atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp (nativePair_tendsto T)

theorem nativePair_norm_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ‖IBMSineAverageWeakGradient.nativePair T n‖)
      atTop (𝓝 ‖gradient T‖) := (nativePair_tendsto T).norm

attribute [local irreducible] gradient IBMSineAverageWeakGradient.nativePair
  IBMIntrinsicGraphDual.embed IBMIntrinsicGraphDual.weakDerivative

theorem native_dual_tendsto (T : ℝ≥0) :
    Tendsto (fun n => IBMIntrinsicGraphDual.embed (IBMSineAverageWeakGradient.nativePair T n))
      atTop (𝓝 (IBMIntrinsicGraphDual.weakDerivative (IBMSineAverageSimpson.average T))) := by
  have ht := IBMIntrinsicGraphDual.embed.continuous.continuousAt.tendsto.comp (nativePair_tendsto T)
  exact ht.mono_right (le_of_eq (congrArg
    (fun L : StrongDual ℝ IBMIntrinsicGraphDual.Tests => 𝓝 L) (gradient_represents T)))

/-- The original actual stochastic pairing error is controlled by the native
gradient error times the FIELD norm, without a bound on the divergence output. -/
theorem actual_divergence_error (T : ℝ≥0) (n : ℕ) (v : jointDivergence.domain) :
    |inner ℝ (IBMSineAverageWeakGradient.nativePair T n) (v : JointFieldSpace) -
      (∫ p, (∫ t in (0:ℝ)..(T:ℝ), Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)) *
        ((jointDivergence v : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure)| ≤
          ‖IBMSineAverageWeakGradient.nativePair T n - gradient T‖ * ‖(v : JointFieldSpace)‖ := by
  rw [← actual_integration_by_parts T v,← inner_sub_left]
  exact abs_real_inner_le_norm _ _

theorem actual_divergence_error_unit (T : ℝ≥0) (n : ℕ) (v : jointDivergence.domain)
    (hv : ‖(v : JointFieldSpace)‖ ≤ 1) :
    |inner ℝ (IBMSineAverageWeakGradient.nativePair T n) (v : JointFieldSpace) -
      (∫ p, (∫ t in (0:ℝ)..(T:ℝ), Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)) *
        ((jointDivergence v : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure)| ≤
          ‖IBMSineAverageWeakGradient.nativePair T n - gradient T‖ := by
  exact (actual_divergence_error T n v).trans
    ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans_eq (mul_one _))

/-- One approximation index works simultaneously for ALL adjoint-domain
tests in the field unit ball, even with unbounded divergence norms. -/
theorem actual_divergence_error_uniform (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ v : jointDivergence.domain, ‖(v : JointFieldSpace)‖ ≤ 1 →
      |inner ℝ (IBMSineAverageWeakGradient.nativePair T n) (v : JointFieldSpace) -
        (∫ p, (∫ t in (0:ℝ)..(T:ℝ), Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)) *
          ((jointDivergence v : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure)| < ε := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((nativePair_error_tendsto T).eventually (gt_mem_nhds hε))
  exact ⟨N,fun n hn v hv => (actual_divergence_error_unit T n v hv).trans_lt (hN n hn)⟩

/-- Uniformly bounded FIELD probes may vary with n. Their divergences need
not have a common bound; each actual integral uses its own adjoint-domain test. -/
theorem moving_actual_divergence_error_tendsto (T : ℝ≥0)
    (v : ℕ → jointDivergence.domain) (M : ℝ) (hv : ∀ n, ‖(v n : JointFieldSpace)‖ ≤ M) :
    Tendsto (fun n => |inner ℝ (IBMSineAverageWeakGradient.nativePair T n) (v n : JointFieldSpace) -
      (∫ p, (∫ t in (0:ℝ)..(T:ℝ), Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)) *
        ((jointDivergence (v n) : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure)|)
          atTop (𝓝 0) := by
  have hb (n : ℕ) := (actual_divergence_error T n (v n)).trans
    (mul_le_mul_of_nonneg_left (hv n) (norm_nonneg _))
  have ht : Tendsto (fun n =>
      ‖IBMSineAverageWeakGradient.nativePair T n - gradient T‖*M) atTop (𝓝 0) := by
    simpa only [zero_mul] using (nativePair_error_tendsto T).mul_const M
  exact squeeze_zero (fun n => abs_nonneg _) hb ht

end OperatorDerivativeRewrite.Foundation.IBMSineAverageStrongJoint
