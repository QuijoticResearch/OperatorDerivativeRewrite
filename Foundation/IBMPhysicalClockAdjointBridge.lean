import Foundation.IBMPhysicalPointSlope
import Foundation.IBMClockGraphDualLimit
import Foundation.IBMIntrinsicGraphDual
import Foundation.GaussianQuadraticSourceHodge
import Foundation.BochnerLiftAdjointInclusion

/-! A concrete common domain for the physical Wiener test dual and ORIGINAL
IBM clock/intrinsic adjoints. Both adjoint memberships are proved. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalClockAdjointBridge
open InfiniteGaussian IBMPhysicalWeakWiener IBMSchwartzWeakWienerClosure
open IBMFirstSourceClockGraph IBMPhysicalPointSlope GaussianQuadraticSourceHodge
open IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

def field (L : Tests) (a b : CoefficientSpace) : VectorSpace :=
  BochnerClosedOperator.tensor gaussianProduct (testNoise L)
    (scalarTensor a (firstChaosEmbedding b))

def output (L : Tests) (a b : CoefficientSpace) : ScalarSpace :=
  BochnerClosedOperator.tensor gaussianProduct (testNoise L) (mixedTarget a b)

theorem adjoint_graph (L : Tests) (a b : CoefficientSpace) :
    (field L a b, output L a b) ∈ IBMClockGraphDualLimit.Clock.adjoint.graph :=
  LinearPMap.le_graph_of_le
    (BochnerLiftAdjointInclusion.lift_adjoint_le gaussianProduct closedCylindricalDerivative
      closedCylindricalDerivative_dense_domain)
    (BochnerClosedOperator.tensor_graph gaussianProduct hilbertDivergence (testNoise L)
      _ _ (mixed_divergence_graph a b))

theorem adjoint_mem (L : Tests) (a b : CoefficientSpace) :
    field L a b ∈ IBMClockGraphDualLimit.Clock.adjoint.domain :=
  LinearPMap.mem_domain_of_mem_graph (adjoint_graph L a b)

theorem adjoint_value (L : Tests) (a b : CoefficientSpace) :
    IBMClockGraphDualLimit.Clock.adjoint ⟨field L a b, adjoint_mem L a b⟩ = output L a b :=
  ((IBMClockGraphDualLimit.Clock.adjoint.image_iff (adjoint_mem L a b)).mpr
    (adjoint_graph L a b)).symm

theorem field_eq_gradientMap (L : Tests) (a b : CoefficientSpace) :
    field L a b = gradientMap a
      (BochnerClosedOperator.tensor gaussianProduct (testNoise L) (firstChaosEmbedding b)) := by
  apply Lp.ext
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct (testNoise L)
      (scalarTensor a (firstChaosEmbedding b)),
    (IBMClockAverageCandidate.tensorBilinear a).coeFn_compLpL
      (BochnerClosedOperator.tensor gaussianProduct (testNoise L) (firstChaosEmbedding b)),
    BochnerClosedOperator.tensor_coeFn gaussianProduct (testNoise L) (firstChaosEmbedding b)]
    with X hf hg ht
  change field L a b X = _ at hf
  change gradientMap a _ X = _ at hg
  rw [hf, hg, IBMClockAverageCandidate.tensorBilinear_eq, ht, map_smul]

theorem native_evaluation_inner (F : ScalarSpace) (L : Tests) (ζ : GaussianL2) :
    inner ℝ (evaluate L (nativeField F)) ζ =
      inner ℝ F (BochnerClosedOperator.tensor gaussianProduct ζ (testNoise L)) := by
  rw [L2_inner_eq_integral, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.apply ℝ ℝ L).coeFn_compLpL (nativeField F),
    native.coeFn_compLpL F, BochnerClosedOperator.tensor_coeFn gaussianProduct ζ (testNoise L)]
    with Y he hn ht
  change evaluate L (nativeField F) Y = nativeField F Y L at he
  change nativeField F Y = native (F Y) at hn
  rw [he, hn, native_apply, ht, real_inner_smul_right, Real.inner_apply, mul_comm]

theorem finite_gradient_pairing (n : ℕ) (t : ℝ≥0) (L : Tests) (a b : CoefficientSpace) :
    inner ℝ (clockGradient n t) (field L a b) =
      inner ℝ (evaluate L (nativeField (signedSource n t))) (firstChaosEmbedding b) *
        inner ℝ (IBMClockAverageCandidate.direction t) a := by
  rw [clockGradient, field_eq_gradientMap, gradientMap_inner, native_evaluation_inner]
  have he := flip.inner_map_map (signedSource n t)
    (BochnerClosedOperator.tensor gaussianProduct (firstChaosEmbedding b) (testNoise L))
  rw [flip_tensor] at he
  rw [he]

theorem physical_pairing_limit (t : ℝ≥0) (L : Tests) (a b : CoefficientSpace) :
    Tendsto (fun n => inner ℝ (clockGradient n t) (field L a b)) atTop
      (nhds (inner ℝ (evaluate L (slopeLimit t)) (firstChaosEmbedding b) *
        inner ℝ (IBMClockAverageCandidate.direction t) a)) := by
  simp only [finite_gradient_pairing]
  exact (((evaluate L).continuous.tendsto _ |>.comp (native_slope_tendsto t)).inner
    (𝕜 := ℝ) tendsto_const_nhds).mul_const _

theorem clock_adjoint_bridge (t : ℝ≥0) (ht : 0 < t) (L : Tests) (a b : CoefficientSpace) :
    IBMClockGraphDualLimit.pointDerivative t
      (ClosedOperatorGraphDualDerivative.testOf IBMClockGraphDualLimit.Clock
        IBMClockGraphDualLimit.clock_dense ⟨field L a b, adjoint_mem L a b⟩) =
      inner ℝ (evaluate L (slopeLimit t)) (firstChaosEmbedding b) *
        inner ℝ (IBMClockAverageCandidate.direction t) a := by
  have hg := (IBMClockGraphDualLimit.clock_gradient_dual_limit t ht)
  have he := ((ContinuousLinearMap.apply ℝ ℝ
    (ClosedOperatorGraphDualDerivative.testOf IBMClockGraphDualLimit.Clock
        IBMClockGraphDualLimit.clock_dense
          ⟨field L a b, adjoint_mem L a b⟩)).continuous.tendsto _).comp hg
  have he' : Tendsto (fun n => inner ℝ (clockGradient n t) (field L a b)) atTop
      (nhds (IBMClockGraphDualLimit.pointDerivative t
        (ClosedOperatorGraphDualDerivative.testOf IBMClockGraphDualLimit.Clock
          IBMClockGraphDualLimit.clock_dense ⟨field L a b, adjoint_mem L a b⟩))) := he
  exact tendsto_nhds_unique he' (physical_pairing_limit t L a b)

theorem clock_inner_bridge (t : ℝ≥0) (ht : 0 < t) (L : Tests) (a b : CoefficientSpace) :
    inner ℝ (IBMClockGraphDualLimit.point t)
      (IBMClockGraphDualLimit.Clock.adjoint ⟨field L a b, adjoint_mem L a b⟩) =
      inner ℝ (evaluate L (slopeLimit t)) (firstChaosEmbedding b) *
        inner ℝ (IBMClockAverageCandidate.direction t) a := by
  have h := clock_adjoint_bridge t ht L a b
  rw [IBMClockGraphDualLimit.pointDerivative_apply_test] at h
  exact h

theorem clock_point_transport (t : ℝ≥0) :
    clockUnitary (intrinsicCurve t : JointL2) = IBMClockGraphDualLimit.point t := rfl

theorem clock_pairing_transport (t : ℝ≥0) (w : ScalarSpace) :
    inner ℝ (intrinsicCurve t : JointL2) (clockUnitary.symm w) =
      inner ℝ (IBMClockGraphDualLimit.point t) w := by
  have hi := clockUnitary.inner_map_map (intrinsicCurve t : JointL2) (clockUnitary.symm w)
  rw [clockUnitary.apply_symm_apply, clock_point_transport] at hi
  exact hi.symm

local instance : SeminormedAddCommGroup IBMIntrinsicGraphDual.Tests := inferInstance
local instance : NormedSpace ℝ IBMIntrinsicGraphDual.Tests := inferInstance
attribute [local irreducible] jointDerivative intrinsicCurve field slopeLimit
  sourceDerivative clockDerivative pairField
  IBMIntrinsicGraphDual.pointDerivative IBMIntrinsicGraphDual.testOf

theorem ambient_clock_compatibility (g : IntrinsicSpace)
    (v : clockDerivative.adjoint.domain) :
    ∃ hp : pairField 0 (v : FieldSpace) ∈ jointDivergence.domain,
      inner ℝ g (jointDivergence ⟨pairField 0 (v : FieldSpace), hp⟩) =
          inner ℝ (g : JointL2) (clockDerivative.adjoint v) := by
  have hex := ambient_pair_divergence
    (0 : sourceDerivative.adjoint.domain) v
  simp only [Submodule.coe_zero] at hex
  obtain ⟨hp, hv⟩ := hex
  refine ⟨hp, ?_⟩
  rw [hv, sourceDerivative.adjoint.map_zero,
    zero_add, real_inner_comm]
  exact (IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right g _).trans
    (real_inner_comm _ _)

theorem intrinsic_adjoint_bridge (t : ℝ≥0) (ht : 0 < t) (L : Tests)
    (a b : CoefficientSpace) :
    ∃ hp : pairField 0 (field L a b) ∈ jointDivergence.domain,
      inner ℝ (intrinsicCurve t)
        (jointDivergence ⟨pairField 0 (field L a b), hp⟩) =
          inner ℝ (evaluate L (slopeLimit t)) (firstChaosEmbedding b) *
            inner ℝ (IBMClockAverageCandidate.direction t) a := by
  have hc : field L a b ∈ clockDerivative.adjoint.domain := by
    rw [clock_adjoint_domain]
    exact adjoint_mem L a b
  have hex := ambient_clock_compatibility (intrinsicCurve t) ⟨field L a b, hc⟩
  obtain ⟨hp, hv⟩ := hex
  refine ⟨hp, hv.trans ?_⟩
  rw [clock_adjoint_apply _ hc (adjoint_mem L a b), clock_pairing_transport]
  exact clock_inner_bridge t ht L a b

end OperatorDerivativeRewrite.Foundation.IBMPhysicalClockAdjointBridge
