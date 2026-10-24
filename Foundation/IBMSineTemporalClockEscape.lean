import Foundation.IBMSineTemporalRegularization

/-! Temporal smoothing recovers actual sine(IBM_T) and its scenery gradient,
while its ORIGINAL clock gradient necessarily escapes. The graph-dual limit
remains a genuine nonrepresentable actual stochastic functional. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineTemporalClockEscape
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMActualSineDomainObstruction IBMSineTemporalRegularization
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] regularized jointDerivative sinePoint sineDerivative
  IBMIntrinsicGraphDual.embed IBMIntrinsicGraphDual.weakDerivative

theorem joint_norm_escape (T : ℝ≥0) (hT : 0 < T) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hne : ∀ n, e n ≠ 0) :
    Tendsto (fun n => ‖jointDerivative (regularized T (e n))‖) atTop atTop :=
  sine_graph_norm_escape T hT (fun n => regularized T (e n)) (value_tendsto T hT e he hne)

theorem clock_norm_escape (T : ℝ≥0) (hT : 0 < T) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hne : ∀ n, e n ≠ 0) :
    Tendsto (fun n => ‖jointDerivative (regularized T (e n)) 1‖) atTop atTop := by
  have hn : clockUnitary (sinePoint T : JointL2) ∉ IBMClockGraphDualLimit.Clock.domain :=
    sinePoint_not_clockDomain T hT
  apply ClosedOperatorEscapeEnergy.output_norm_tendsto_atTop IBMClockGraphDualLimit.Clock
    IBMClockGraphDualLimit.clock_closed IBMClockGraphDualLimit.clock_dense
    (fun n => IBMIntrinsicChainRule.clock_partial_graph (regularized T (e n))) _ hn
  exact clockUnitary.continuous.continuousAt.tendsto.comp
    (IntrinsicSpace.subtypeL.continuous.continuousAt.tendsto.comp (value_tendsto T hT e he hne))

theorem graph_dual_tendsto (T : ℝ≥0) (hT : 0 < T) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hne : ∀ n, e n ≠ 0) :
    Tendsto (fun n => IBMIntrinsicGraphDual.embed (jointDerivative (regularized T (e n)))) atTop
      (𝓝 (sineDerivative T)) := by
  simpa only [sineDerivative] using
    IBMIntrinsicGraphDual.graph_dual_limit (sinePoint T) (fun n => regularized T (e n))
      (value_tendsto T hT e he hne)

theorem dual_limit_not_representable (T : ℝ≥0) (hT : 0 < T) :
    ¬ ∃ V : JointFieldSpace, IBMIntrinsicGraphDual.embed V = sineDerivative T :=
  sineDerivative_not_representable T hT

theorem actual_stochastic_pairing (T : ℝ≥0) (e : ℝ) (v : jointDivergence.domain) :
    inner ℝ (jointDerivative (regularized T e)) (v : JointFieldSpace) =
      ∫ p, (e⁻¹ *
        ((∫ t in (0:ℝ)..(((T:ℝ)+e).toNNReal:ℝ),
          Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)) -
         (∫ t in (0:ℝ)..(T:ℝ), Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)))) *
        ((jointDivergence v : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure := by
  have h := congrArg (fun L : StrongDual ℝ IBMIntrinsicGraphDual.Tests =>
    L (IBMIntrinsicGraphDual.testOf v)) (IBMIntrinsicGraphDual.original_graph (regularized T e))
  have hv : IBMIntrinsicGraphDual.embed (jointDerivative (regularized T e))
      (IBMIntrinsicGraphDual.testOf v) =
        inner ℝ (jointDerivative (regularized T e)) (v : JointFieldSpace) := by
    unfold IBMIntrinsicGraphDual.embed IBMIntrinsicGraphDual.testOf
    rfl
  exact hv.symm.trans (h.trans (IBMIntrinsicGraphDual.actual_pairing
    (regularized T e : IntrinsicSpace) _ (regularized_actual_ae T e) v))

theorem point_pairing_limit (T : ℝ≥0) (hT : 0 < T) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hne : ∀ n, e n ≠ 0) (v : jointDivergence.domain) :
    Tendsto (fun n => inner ℝ (jointDerivative (regularized T (e n))) (v : JointFieldSpace))
      atTop (𝓝 (∫ p, Real.sin (IBMConstructedSources.ibmValue T p) *
        ((jointDivergence v : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure)) := by
  have ht := (value_tendsto T hT e he hne).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := (jointDivergence v : IntrinsicSpace)))
  have heq (n : ℕ) : inner ℝ (regularized T (e n) : IntrinsicSpace) (jointDivergence v) =
      inner ℝ (jointDerivative (regularized T (e n))) (v : JointFieldSpace) :=
    ClosedOperatorEscapeEnergy.graph_pairing jointDerivative jointDerivative_dense
      (jointDerivative.mem_graph (regularized T (e n))) v
  have hp : inner ℝ (sinePoint T) (jointDivergence v) =
      ∫ p, Real.sin (IBMConstructedSources.ibmValue T p) *
        ((jointDivergence v : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure := by
    simpa only [sineDerivative,IBMIntrinsicGraphDual.test_pairing] using
      sineDerivative_actual_pairing T v
  simpa only [heq,hp] using ht

end OperatorDerivativeRewrite.Foundation.IBMSineTemporalClockEscape
