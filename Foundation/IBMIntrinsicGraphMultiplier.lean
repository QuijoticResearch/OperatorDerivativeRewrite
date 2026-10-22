import Foundation.IBMIntrinsicWeakLeibniz
import Mathlib.Analysis.Normed.Operator.Banach

/-! Bounded multiplication on the FULL intrinsic IBM adjoint graph.
The original weighted-domain theorem supplies membership; closed graph supplies
continuity in the actual Hilbert graph norm. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicGraphMultiplier
open InfiniteGaussian (CoefficientSpace)
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicGraphDual
open IBMNativeFieldMultiplier IBMNativeProductOperators IBMIntrinsicWeakLeibniz
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] IBMJointIntrinsicDerivative.jointDerivative

abbrev testField : Tests →L[ℝ] JointFieldSpace :=
  ClosedOperatorGraphDualDerivative.field jointDerivative jointDerivative_dense

abbrev testValue : Tests →L[ℝ] IntrinsicSpace :=
  ClosedOperatorGraphDualDerivative.value jointDerivative jointDerivative_dense

theorem testField_injective : Function.Injective testField := by
  intro x y h
  have hv := jointDivergence.mem_graph_snd_inj
    (ClosedOperatorGraphDualDerivative.test_graph jointDerivative jointDerivative_dense x)
    (ClosedOperatorGraphDualDerivative.test_graph jointDerivative jointDerivative_dense y) h
  apply Subtype.ext
  apply (WithLp.equiv 2 (JointFieldSpace × IntrinsicSpace)).injective
  exact Prod.ext h hv

def asDomain (w : Tests) : jointDivergence.domain :=
  ⟨testField w, LinearPMap.mem_domain_of_mem_graph
    (ClosedOperatorGraphDualDerivative.test_graph jointDerivative jointDerivative_dense w)⟩

theorem testOf_asDomain (w : Tests) : testOf (asDomain w) = w :=
  testField_injective rfl

variable (f : jointDerivative.domain) (C : ℝ) (hC : 0 ≤ C)
  (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
  (hDf : ∀ i : Fin 2, MemLp (coordinate i (jointDerivative f i) :
    IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure)

def liftPoint (w : Tests) : Tests := weightedTest f C hC hf hDf (asDomain w)

theorem liftPoint_field (w : Tests) :
    testField (liftPoint f C hC hf hDf w) =
      multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) (testField w) := rfl

def liftLinear : Tests →ₗ[ℝ] Tests where
  toFun := liftPoint f C hC hf hDf
  map_add' := by
    intro x y
    apply testField_injective
    simp only [liftPoint_field, map_add]
  map_smul' := by
    intro c x
    apply testField_injective
    simp only [liftPoint_field, map_smul, RingHom.id_apply]

theorem liftLinear_field (w : Tests) :
    testField (liftLinear f C hC hf hDf w) =
      multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) (testField w) := rfl

theorem liftLinear_seqClosedGraph :
    ∀ (u : ℕ → Tests) (x y : Tests), Tendsto u atTop (𝓝 x) →
      Tendsto (liftLinear f C hC hf hDf ∘ u) atTop (𝓝 y) →
        y = liftLinear f C hC hf hDf x := by
  intro u x y hu hv
  apply testField_injective
  have hl := testField.continuous.tendsto y |>.comp hv
  have hr := ((multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf)).comp
    testField).continuous.tendsto x |>.comp hu
  have hr' : Tendsto (fun n => testField (liftLinear f C hC hf hDf (u n))) atTop
      (𝓝 (testField (liftLinear f C hC hf hDf x))) := by
    simpa only [Function.comp_def, liftLinear_field, ContinuousLinearMap.comp_apply] using hr
  exact tendsto_nhds_unique hl hr'

def graphMultiplier : Tests →L[ℝ] Tests :=
  ContinuousLinearMap.ofSeqClosedGraph (liftLinear_seqClosedGraph f C hC hf hDf)

theorem graphMultiplier_field (w : Tests) :
    testField (graphMultiplier f C hC hf hDf w) =
      multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) (testField w) := rfl

theorem graphMultiplier_testOf (v : jointDivergence.domain) :
    graphMultiplier f C hC hf hDf (testOf v) = weightedTest f C hC hf hDf v := by
  apply testField_injective
  rfl

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicGraphMultiplier
