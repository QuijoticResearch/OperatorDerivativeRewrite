import Foundation.IBMSineAverageSourceDomain

/-! A genuine nonlinear path integral in the original intrinsic IBM domain,
with its full adjoint identity and strong-field representation of the
previously constructed Simpson graph-dual limit. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineAverageIntrinsicCalculus
open InfiniteGaussian IBMTimeAveragedObservable IBMJointIntrinsicDerivative
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem average_joint_domain (T : ℝ≥0) :
    IBMSineAverageSimpson.average T ∈ jointDerivative.domain := by
  apply (joint_domain_iff _).mpr
  apply (IBMFiniteAverageCore.mem_intrinsicCore_iff _).mpr
  exact ⟨(IBMSineAverageSimpson.average T).property,
    IBMSineAverageClockDomain.actual_average_clock_domain T,
    IBMSineAverageSourceDomain.actual_average_source_domain T⟩

def domainAverage (T : ℝ≥0) : jointDerivative.domain :=
  ⟨IBMSineAverageSimpson.average T, average_joint_domain T⟩

def gradient (T : ℝ≥0) : JointFieldSpace := jointDerivative (domainAverage T)

theorem average_graph (T : ℝ≥0) :
    (IBMSineAverageSimpson.average T, gradient T) ∈ jointDerivative.graph :=
  jointDerivative.mem_graph (domainAverage T)

theorem gradient_represents (T : ℝ≥0) :
    IBMIntrinsicGraphDual.embed (gradient T) =
      IBMIntrinsicGraphDual.weakDerivative (IBMSineAverageSimpson.average T) :=
  IBMIntrinsicGraphDual.original_graph (domainAverage T)

theorem gradient_unique (T : ℝ≥0) (V : JointFieldSpace)
    (hV : IBMIntrinsicGraphDual.embed V =
      IBMIntrinsicGraphDual.weakDerivative (IBMSineAverageSimpson.average T)) : V = gradient T :=
  IBMIntrinsicGraphDual.embed_injective (hV.trans (gradient_represents T).symm)

section
attribute [local irreducible] gradient IBMSineAverageSimpson.average IBMSineAverageSimpson.value
  IBMIntrinsicGraphDual.embed IBMIntrinsicGraphDual.weakDerivative

theorem simpson_derivative_tendsto (T : ℝ≥0) :
    Tendsto (fun n => IBMIntrinsicGraphDual.weakDerivative (IBMSineAverageSimpson.value T n)) atTop
      (𝓝 (IBMIntrinsicGraphDual.embed (gradient T))) := by
  apply (IBMSineAverageSimpson.weakDerivative_tendsto T).mono_right
  exact le_of_eq (congrArg (fun L : StrongDual ℝ IBMIntrinsicGraphDual.Tests => 𝓝 L)
    (gradient_represents T).symm)
end

theorem actual_integration_by_parts (T : ℝ≥0) (v : jointDivergence.domain) :
    inner ℝ (gradient T) (v : JointFieldSpace) =
      ∫ p, (∫ t in (0 : ℝ)..(T : ℝ),
        Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)) *
          ((jointDivergence v : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure := by
  have h := congrArg (fun L : StrongDual ℝ IBMIntrinsicGraphDual.Tests =>
    L (IBMIntrinsicGraphDual.testOf v)) (gradient_represents T)
  exact h.trans (IBMIntrinsicGraphDual.actual_pairing (IBMSineAverageSimpson.average T) _
    (IBMSineAverageSimpson.average_actual_ae T) v)

theorem actual_adjoint_product_integrable (T : ℝ≥0) (v : jointDivergence.domain) :
    Integrable (fun p => (∫ t in (0 : ℝ)..(T : ℝ),
      Real.sin (IBMConstructedSources.ibmValue t.toNNReal p)) *
        ((jointDivergence v : IntrinsicSpace) : JointL2) p) IBMSourceLaws.jointMeasure :=
  IBMIntrinsicGraphDual.actual_pairing_integrable (IBMSineAverageSimpson.average T) _
    (IBMSineAverageSimpson.average_actual_ae T) v

end OperatorDerivativeRewrite.Foundation.IBMSineAverageIntrinsicCalculus
