import Foundation.IBMSineAverageIntrinsicCalculus
import Foundation.ClosedOperatorWeakGraphLimit

/-! Genuine weak L2 convergence of the original native clock and source
approximants to the two channels of the actual IBM sine-average gradient. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineAverageWeakGradient
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMSineAverageIntrinsicCalculus IBMClockGraphDualLimit
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem clock_graph (T : ℝ≥0) :
    (clockUnitary (IBMSineAverageSimpson.average T : JointL2), gradient T 1) ∈ Clock.graph :=
  IBMIntrinsicChainRule.clock_partial_graph (domainAverage T)

theorem source_graph (T : ℝ≥0) :
    (sourceUnitary (IBMSineAverageSimpson.average T : JointL2), gradient T 0) ∈ Clock.graph :=
  IBMIntrinsicChainRule.source_partial_graph (domainAverage T)

attribute [local irreducible] gradient IBMNonlinearClockAverageGraph.average
  IBMNonlinearClockAverageGraph.averageGradient IBMSineAverageSourceDomain.gradientSum

theorem clock_value_tendsto (T : ℝ≥0) :
    Tendsto (fun n => clockUnitary (IBMNonlinearClockAverageGraph.average n T)) atTop
      (𝓝 (clockUnitary (IBMSineAverageSimpson.average T : JointL2))) := by
  have hu := clockUnitary.continuous.continuousAt.tendsto.comp
    (IBMSineAverageClockDomain.average_tendsto T.property)
  have he := congrArg clockUnitary (IBMSineAverageClockDomain.limitAverage_eq_actual T)
  exact he ▸ hu

theorem source_value_tendsto (T : ℝ≥0) :
    Tendsto (fun n => IBMBochnerTimeQuadrature.rightSum IBMSineAverageSourceDomain.valueCurve T (n + 1))
      atTop (𝓝 (sourceUnitary (IBMSineAverageSimpson.average T : JointL2))) :=
  (IBMSineAverageSourceDomain.valueCurve_integral T) ▸
    IBMBochnerTimeQuadrature.rightSum_tendsto IBMSineAverageSourceDomain.valueCurve
      IBMSineAverageSourceDomain.valueCurve_continuous T.property

theorem clock_pairing_tendsto (T : ℝ≥0) (w : FieldSpace) :
    Tendsto (fun n => inner ℝ (IBMNonlinearClockAverageGraph.averageGradient n T) w) atTop
      (𝓝 (inner ℝ (gradient T 1) w)) :=
  ClosedOperatorWeakGraphLimit.pairing_tendsto Clock clock_closed clock_dense
    (fun n => IBMNonlinearClockAverageGraph.average_clock_graph n T.property) (clock_graph T)
    (clock_value_tendsto T)
    (Real.sqrt (8 * IBMFoldedTransitionBound.peak 1 * (T : ℝ) ^ 2 * Real.sqrt T + 4 * (T : ℝ) ^ 3))
    (Real.sqrt_nonneg _) (fun n => IBMNonlinearClockAverageGraph.averageGradient_norm_bound n T.property) w

theorem source_pairing_tendsto (T : ℝ≥0) (w : FieldSpace) :
    Tendsto (fun n => inner ℝ (IBMSineAverageSourceDomain.gradientSum T n) w) atTop
      (𝓝 (inner ℝ (gradient T 0) w)) := by
  obtain ⟨C, hC, hb⟩ := IBMSineAverageSourceDomain.sourceGradient_bounded T
  exact ClosedOperatorWeakGraphLimit.pairing_tendsto Clock clock_closed clock_dense
    (IBMSineAverageSourceDomain.quadrature_graph T) (source_graph T) (source_value_tendsto T)
    ((T : ℝ) * C) (mul_nonneg T.property hC)
    (IBMSineAverageSourceDomain.gradientSum_norm_le T hC hb) w

theorem clock_weak_tendsto (T : ℝ≥0) :
    Tendsto (fun n => (IBMNonlinearClockAverageGraph.averageGradient n T : WeakBilin (innerₗ FieldSpace)))
      atTop (@nhds (WeakBilin (innerₗ FieldSpace))
        (WeakBilin.instTopologicalSpace (innerₗ FieldSpace)) (gradient T 1)) :=
  ClosedOperatorWeakGraphLimit.weak_tendsto Clock clock_closed clock_dense
    (fun n => IBMNonlinearClockAverageGraph.average_clock_graph n T.property) (clock_graph T)
    (clock_value_tendsto T)
    (Real.sqrt (8 * IBMFoldedTransitionBound.peak 1 * (T : ℝ) ^ 2 * Real.sqrt T + 4 * (T : ℝ) ^ 3))
    (Real.sqrt_nonneg _) (fun n => IBMNonlinearClockAverageGraph.averageGradient_norm_bound n T.property)

theorem source_weak_tendsto (T : ℝ≥0) :
    Tendsto (fun n => (IBMSineAverageSourceDomain.gradientSum T n : WeakBilin (innerₗ FieldSpace)))
      atTop (@nhds (WeakBilin (innerₗ FieldSpace))
        (WeakBilin.instTopologicalSpace (innerₗ FieldSpace)) (gradient T 0)) := by
  obtain ⟨C, hC, hb⟩ := IBMSineAverageSourceDomain.sourceGradient_bounded T
  exact ClosedOperatorWeakGraphLimit.weak_tendsto Clock clock_closed clock_dense
    (IBMSineAverageSourceDomain.quadrature_graph T) (source_graph T) (source_value_tendsto T)
    ((T : ℝ) * C) (mul_nonneg T.property hC)
    (IBMSineAverageSourceDomain.gradientSum_norm_le T hC hb)

theorem actual_clock_norm_bound (T : ℝ≥0) :
    ‖gradient T 1‖ ≤
      Real.sqrt (8 * IBMFoldedTransitionBound.peak 1 * (T : ℝ) ^ 2 * Real.sqrt T + 4 * (T : ℝ) ^ 3) := by
  obtain ⟨hf, hb⟩ := IBMClockAverageGraph.clock_domain_of_bounded_graph_limit
    _ _ _ _ (Real.sqrt_nonneg _)
    (fun n => IBMNonlinearClockAverageGraph.average_clock_graph n T.property)
    (clock_value_tendsto T)
    (fun n => IBMNonlinearClockAverageGraph.averageGradient_norm_bound n T.property)
  have he : Clock ⟨_, hf⟩ = gradient T 1 :=
    Clock.mem_graph_snd_inj (Clock.mem_graph _) (clock_graph T) rfl
  exact he ▸ hb

theorem actual_clock_energy (T : ℝ≥0) :
    ‖gradient T 1‖ ^ 2 ≤
      8 * IBMFoldedTransitionBound.peak 1 * (T : ℝ) ^ 2 * Real.sqrt T + 4 * (T : ℝ) ^ 3 := by
  have h0 := (sq_nonneg ‖IBMNonlinearClockAverageGraph.averageGradient 0 T‖).trans
    (IBMNonlinearClockAverageGraph.averageGradient_uniform_energy 0 T.property)
  nlinarith [actual_clock_norm_bound T, Real.sq_sqrt h0, norm_nonneg (gradient T 1),
    Real.sqrt_nonneg (8 * IBMFoldedTransitionBound.peak 1 * (T : ℝ) ^ 2 * Real.sqrt T + 4 * (T : ℝ) ^ 3)]

/-- Both actual native approximants in their original source/clock channels.
This pairing does not assert that they share one finite-stage graph input. -/
def nativePair (T : ℝ≥0) (n : ℕ) : JointFieldSpace :=
  pairField (IBMSineAverageSourceDomain.gradientSum T n)
    (IBMNonlinearClockAverageGraph.averageGradient n T)

theorem joint_pairing_tendsto (T : ℝ≥0) (w : JointFieldSpace) :
    Tendsto (fun n => inner ℝ (nativePair T n) w) atTop (𝓝 (inner ℝ (gradient T) w)) := by
  have h := (source_pairing_tendsto T (w 0)).add (clock_pairing_tendsto T (w 1))
  simpa [nativePair, pairField, PiLp.inner_apply, Fin.sum_univ_two] using h

theorem joint_weak_tendsto (T : ℝ≥0) :
    Tendsto (fun n => (nativePair T n : WeakBilin (innerₗ JointFieldSpace))) atTop
      (@nhds (WeakBilin (innerₗ JointFieldSpace))
        (WeakBilin.instTopologicalSpace (innerₗ JointFieldSpace)) (gradient T)) := by
  have hi : Function.Injective (innerₗ JointFieldSpace) := by
    intro a b he
    have hs : inner ℝ (a - b) (a - b) = 0 := by
      rw [inner_sub_left]
      exact sub_eq_zero.mpr (congrArg (fun L : JointFieldSpace →ₗ[ℝ] ℝ => L (a - b)) he)
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hs)
  exact (WeakBilin.tendsto_iff_forall_eval_tendsto (innerₗ JointFieldSpace) hi).mpr
    (joint_pairing_tendsto T)

theorem actual_divergence_pairing_tendsto (T : ℝ≥0) (v : jointDivergence.domain) :
    Tendsto (fun n => inner ℝ (nativePair T n) (v : JointFieldSpace)) atTop
      (𝓝 (∫ p, (∫ t in (0 : ℝ)..(T : ℝ),
        Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)) *
          ((jointDivergence v : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure)) := by
  apply (joint_pairing_tendsto T (v : JointFieldSpace)).mono_right
  exact le_of_eq (congrArg (fun x : ℝ => 𝓝 x) (actual_integration_by_parts T v))

end OperatorDerivativeRewrite.Foundation.IBMSineAverageWeakGradient
