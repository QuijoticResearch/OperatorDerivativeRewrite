import Foundation.ClosedOperatorGraphDualDerivative
import Foundation.IBMPointClockDomainObstruction

/-! Generalized derivatives for the ACTUAL intrinsic IBM operator, using its
full adjoint domain and genuine observable-domain approximations. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicGraphDual
open InfiniteGaussian IBMTimeAveragedObservable IBMJointIntrinsicDerivative
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

abbrev Tests := ClosedOperatorGraphDualDerivative.Tests jointDerivative jointDerivative_dense

def weakDerivative : IntrinsicSpace →L[ℝ] StrongDual ℝ Tests :=
  ClosedOperatorGraphDualDerivative.derivative jointDerivative jointDerivative_dense

def embed : JointFieldSpace →L[ℝ] StrongDual ℝ Tests :=
  ClosedOperatorGraphDualDerivative.embed jointDerivative jointDerivative_dense

def testOf (v : jointDivergence.domain) : Tests :=
  ClosedOperatorGraphDualDerivative.testOf jointDerivative jointDerivative_dense v

theorem weakDerivative_norm (f : IntrinsicSpace) : ‖weakDerivative f‖ ≤ ‖f‖ :=
  ClosedOperatorGraphDualDerivative.derivative_norm_le _ _ _

theorem original_graph (f : jointDerivative.domain) :
    embed (jointDerivative f) = weakDerivative (f : IntrinsicSpace) :=
  ClosedOperatorGraphDualDerivative.graph_agreement _ _ (jointDerivative.mem_graph f)

theorem embed_injective : Function.Injective embed :=
  ClosedOperatorGraphDualDerivative.embed_injective _ jointDerivative_closed jointDerivative_dense

theorem representable_iff_domain (f : IntrinsicSpace) :
    (∃ V : JointFieldSpace, embed V = weakDerivative f) ↔ f ∈ jointDerivative.domain :=
  ClosedOperatorGraphDualDerivative.representable_iff_domain _ jointDerivative_closed _ f

theorem test_pairing (f : IntrinsicSpace) (v : jointDivergence.domain) :
    weakDerivative f (testOf v) = inner ℝ f (jointDivergence v) := rfl

theorem actual_pairing (f : IntrinsicSpace) (X : IBMSourceLaws.JointSample → ℝ)
    (hX : (f : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] X) (v : jointDivergence.domain) :
    weakDerivative f (testOf v) =
      ∫ ω, X ω * ((jointDivergence v : IntrinsicSpace) : JointL2) ω
        ∂IBMSourceLaws.jointMeasure := by
  change inner ℝ (f : JointL2) ((jointDivergence v : IntrinsicSpace) : JointL2) = _
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [hX] with ω hx
  rw [hx, Real.inner_apply]

theorem actual_pairing_integrable (f : IntrinsicSpace) (X : IBMSourceLaws.JointSample → ℝ)
    (hX : (f : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] X) (v : jointDivergence.domain) :
    Integrable (fun ω => X ω * ((jointDivergence v : IntrinsicSpace) : JointL2) ω)
      IBMSourceLaws.jointMeasure := by
  apply ((Lp.memLp (f : JointL2)).integrable_mul
    (Lp.memLp ((jointDivergence v : IntrinsicSpace) : JointL2))).congr
  filter_upwards [hX] with ω hx
  simp only [Pi.mul_apply, hx]

theorem domain_approximation (f : IntrinsicSpace) :
    ∃ u : ℕ → jointDerivative.domain,
      Tendsto (fun n => (u n : IntrinsicSpace)) atTop (𝓝 f) := by
  have hf : f ∈ closure (jointDerivative.domain : Set IntrinsicSpace) := by
    rw [jointDerivative_dense.closure_eq]
    exact Set.mem_univ f
  obtain ⟨x, hx, ht⟩ := mem_closure_iff_seq_limit.mp hf
  exact ⟨fun n => ⟨x n, hx n⟩, ht⟩

theorem graph_dual_limit (f : IntrinsicSpace) (u : ℕ → jointDerivative.domain)
    (hu : Tendsto (fun n => (u n : IntrinsicSpace)) atTop (𝓝 f)) :
    Tendsto (fun n => embed (jointDerivative (u n))) atTop (𝓝 (weakDerivative f)) :=
  ClosedOperatorGraphDualDerivative.graph_limit _ _ (fun n => jointDerivative.mem_graph (u n)) hu

theorem graph_dual_error (f : IntrinsicSpace) (u : jointDerivative.domain) :
    ‖embed (jointDerivative u) - weakDerivative f‖ ≤ ‖(u : IntrinsicSpace) - f‖ :=
  ClosedOperatorGraphDualDerivative.graph_error_bound _ _ (jointDerivative.mem_graph u) f

def pointDerivative (t : ℝ≥0) : StrongDual ℝ Tests := weakDerivative (intrinsicCurve t)

theorem pointDerivative_continuous : Continuous pointDerivative :=
  weakDerivative.continuous.comp intrinsicCurve_continuous

theorem pointDerivative_not_representable (t : ℝ≥0) (ht : 0 < t) :
    ¬ ∃ V : JointFieldSpace, embed V = pointDerivative t := by
  intro h
  exact IBMPointClockDomainObstruction.actual_point_not_joint_domain t ht
    ((representable_iff_domain _).mp h)

theorem pointDerivative_ne_zero (t : ℝ≥0) (ht : 0 < t) : pointDerivative t ≠ 0 :=
  ClosedOperatorGraphDualDerivative.derivative_ne_zero_of_not_domain _ jointDerivative_closed _
    (IBMPointClockDomainObstruction.actual_point_not_joint_domain t ht)

theorem point_actual_pairing (t : ℝ≥0) (v : jointDivergence.domain) :
    pointDerivative t (testOf v) =
      ∫ ω, IBMConstructedSources.ibmValue t ω *
        ((jointDivergence v : IntrinsicSpace) : JointL2) ω ∂IBMSourceLaws.jointMeasure :=
  actual_pairing (intrinsicCurve t) _ (joint_point_actual_ae t) v

theorem point_actual_integrable (t : ℝ≥0) (v : jointDivergence.domain) :
    Integrable (fun ω => IBMConstructedSources.ibmValue t ω *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω) IBMSourceLaws.jointMeasure :=
  actual_pairing_integrable (intrinsicCurve t) _ (joint_point_actual_ae t) v

theorem point_graph_norm_escape (t : ℝ≥0) (ht : 0 < t)
    (u : ℕ → jointDerivative.domain)
    (hu : Tendsto (fun n => (u n : IntrinsicSpace)) atTop (𝓝 (intrinsicCurve t))) :
    Tendsto (fun n => ‖jointDerivative (u n)‖) atTop atTop :=
  ClosedOperatorEscapeEnergy.output_norm_tendsto_atTop jointDerivative jointDerivative_closed
    jointDerivative_dense
    (fun n => jointDerivative.mem_graph (u n)) hu
    (IBMPointClockDomainObstruction.actual_point_not_joint_domain t ht)

attribute [local irreducible] IBMTimeAveragedObservable.intrinsicCurve
  IBMJointIntrinsicDerivative.jointDerivative IBMIntrinsicOperators.sourceDerivative
  IBMIntrinsicOperators.clockDerivative

theorem ambient_pair_compatibility (g : IntrinsicSpace)
    (a : IBMIntrinsicOperators.sourceDerivative.adjoint.domain)
    (b : IBMIntrinsicOperators.clockDerivative.adjoint.domain) :
    ∃ hp : pairField a b ∈ jointDivergence.domain,
      weakDerivative g (testOf ⟨pairField a b, hp⟩) =
        inner ℝ (g : JointL2)
          (IBMIntrinsicOperators.sourceDerivative.adjoint a +
            IBMIntrinsicOperators.clockDerivative.adjoint b) := by
  exact (ambient_pair_divergence a b).imp fun hp hv => by
    rw [test_pairing, hv, real_inner_comm]
    exact (IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right g _).trans
      (real_inner_comm _ _)

theorem point_observable_graph_approximation (t : ℝ≥0) (ht : 0 < t) :
    ∃ u : ℕ → jointDerivative.domain,
      Tendsto (fun n => (u n : IntrinsicSpace)) atTop (𝓝 (intrinsicCurve t)) ∧
      Tendsto (fun n => embed (jointDerivative (u n))) atTop (𝓝 (pointDerivative t)) ∧
      Tendsto (fun n => ‖jointDerivative (u n)‖) atTop atTop := by
  exact (domain_approximation (intrinsicCurve t)).imp fun u hu =>
    ⟨hu, graph_dual_limit (intrinsicCurve t) u hu, point_graph_norm_escape t ht u hu⟩

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicGraphDual
