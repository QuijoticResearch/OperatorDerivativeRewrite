import Foundation.IBMIntrinsicCoreDensity
import Foundation.ObservableDensityCriterion
import Foundation.AdjointUnitaryTransport

/-! Actual native source/clock operators and densely defined intrinsic IBM
restrictions. Ambient-adjoint inclusions retain their precise one-sided scope. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicOperators
open InfiniteGaussian IBMTimeAveragedObservable IBMFiniteAverageCore IBMIntrinsicCoreDensity
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev FieldSpace := Lp GaussianVectorL2 2 gaussianProduct
abbrev ScalarFieldSpace := Lp GaussianL2 2 gaussianProduct

local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable IBMConstructedSources.clockPath_measurable).completeSpace_coe

def swapEquiv : JointL2 ≃ₗᵢ[ℝ] JointL2 :=
  LinearIsometryEquiv.ofSurjective (ProductL2Curry.swap gaussianProduct gaussianProduct)
    (fun f => ⟨ProductL2Curry.swap gaussianProduct gaussianProduct f,
      IBMNonlinearAverageGraph.swap_swap f⟩)

def clockUnitary : JointL2 ≃ₗᵢ[ℝ] ScalarFieldSpace :=
  ProductL2Curry.curryEquiv gaussianProduct gaussianProduct

def sourceUnitary : JointL2 ≃ₗᵢ[ℝ] ScalarFieldSpace := swapEquiv.trans clockUnitary

def clockDerivative : JointL2 →ₗ.[ℝ] FieldSpace :=
  AdjointUnitaryTransport.pullback clockUnitary partialDerivative

def sourceDerivative : JointL2 →ₗ.[ℝ] FieldSpace :=
  AdjointUnitaryTransport.pullback sourceUnitary partialDerivative

theorem clockDerivative_domain : clockDerivative.domain = clockDomain := by rfl

theorem sourceDerivative_domain : sourceDerivative.domain = sourceDomain := by rfl

theorem clockDerivative_closed : clockDerivative.IsClosed :=
  AdjointUnitaryTransport.pullback_isClosed _ _
    (BochnerClosedOperator.lift_isClosed gaussianProduct _ closedCylindricalDerivative_isClosed)

theorem sourceDerivative_closed : sourceDerivative.IsClosed :=
  AdjointUnitaryTransport.pullback_isClosed _ _
    (BochnerClosedOperator.lift_isClosed gaussianProduct _ closedCylindricalDerivative_isClosed)

theorem partialDerivative_dense : Dense (partialDerivative.domain : Set ScalarFieldSpace) :=
  BochnerClosedOperator.lift_dense_domain gaussianProduct _ closedCylindricalDerivative_dense_domain

theorem clockDerivative_dense : Dense (clockDerivative.domain : Set JointL2) :=
  AdjointUnitaryTransport.pullback_dense_domain _ _ partialDerivative_dense

theorem sourceDerivative_dense : Dense (sourceDerivative.domain : Set JointL2) :=
  AdjointUnitaryTransport.pullback_dense_domain _ _ partialDerivative_dense

def intrinsicClock := ObservableRestriction.derivative clockDerivative IntrinsicSpace
def intrinsicSource := ObservableRestriction.derivative sourceDerivative IntrinsicSpace

theorem restriction_dense_of_core (A : JointL2 →ₗ.[ℝ] FieldSpace)
    (hA : ∀ f ∈ intrinsicCore, f ∈ A.domain) :
    Dense ((ObservableRestriction.derivative A IntrinsicSpace).domain : Set IntrinsicSpace) := by
  apply (ObservableDensityCriterion.derivative_dense_iff_annihilator_zero A IntrinsicSpace).mpr
  intro g hg
  apply Subtype.ext
  apply intrinsic_annihilator_zero (g : JointL2) _ g.property
  rw [Submodule.mem_orthogonal']
  intro f hf
  let fi : IntrinsicSpace := ⟨f, ((mem_intrinsicCore_iff f).mp hf).1⟩
  have hfi : fi ∈ (ObservableRestriction.derivative A IntrinsicSpace).domain := hA f hf
  exact hg ⟨fi, hfi⟩

theorem intrinsicClock_dense : Dense (intrinsicClock.domain : Set IntrinsicSpace) := by
  apply restriction_dense_of_core
  intro f hf
  rw [clockDerivative_domain]
  exact ((mem_intrinsicCore_iff f).mp hf).2.1

theorem intrinsicSource_dense : Dense (intrinsicSource.domain : Set IntrinsicSpace) := by
  apply restriction_dense_of_core
  intro f hf
  rw [sourceDerivative_domain]
  exact ((mem_intrinsicCore_iff f).mp hf).2.2

theorem intrinsicClock_closed : intrinsicClock.IsClosed :=
  ObservableRestriction.derivative_isClosed _ _ clockDerivative_closed

theorem intrinsicSource_closed : intrinsicSource.IsClosed :=
  ObservableRestriction.derivative_isClosed _ _ sourceDerivative_closed

/-- Complete ambient adjoint domains are preserved by native unitary transport. -/
theorem clock_adjoint_domain : clockDerivative.adjoint.domain = partialDerivative.adjoint.domain :=
  AdjointUnitaryTransport.pullback_adjoint_domain _ _ partialDerivative_dense

theorem source_adjoint_domain : sourceDerivative.adjoint.domain = partialDerivative.adjoint.domain :=
  AdjointUnitaryTransport.pullback_adjoint_domain _ _ partialDerivative_dense

theorem clock_adjoint_apply (u : FieldSpace) (hu : u ∈ clockDerivative.adjoint.domain)
    (hp : u ∈ partialDerivative.adjoint.domain) :
    clockDerivative.adjoint ⟨u, hu⟩ = clockUnitary.symm (partialDerivative.adjoint ⟨u, hp⟩) :=
  AdjointUnitaryTransport.pullback_adjoint_apply _ _ partialDerivative_dense _ hu hp

theorem source_adjoint_apply (u : FieldSpace) (hu : u ∈ sourceDerivative.adjoint.domain)
    (hp : u ∈ partialDerivative.adjoint.domain) :
    sourceDerivative.adjoint ⟨u, hu⟩ = sourceUnitary.symm (partialDerivative.adjoint ⟨u, hp⟩) :=
  AdjointUnitaryTransport.pullback_adjoint_apply _ _ partialDerivative_dense _ hu hp

/-- Ambient divergences are valid intrinsic integrands. Full intrinsic adjoint
domains may be larger; equality of those domains is not asserted. -/
theorem clock_source_divergence_mem (u : clockDerivative.adjoint.domain) :
    (u : FieldSpace) ∈ intrinsicClock.adjoint.domain :=
  ObservableProjectedDivergence.source_divergence_mem _ _ clockDerivative_dense intrinsicClock_dense u

theorem source_source_divergence_mem (u : sourceDerivative.adjoint.domain) :
    (u : FieldSpace) ∈ intrinsicSource.adjoint.domain :=
  ObservableProjectedDivergence.source_divergence_mem _ _ sourceDerivative_dense intrinsicSource_dense u

theorem intrinsic_clock_divergence_value (u : clockDerivative.adjoint.domain) :
    intrinsicClock.adjoint ⟨(u : FieldSpace), clock_source_divergence_mem u⟩ =
      IntrinsicSpace.orthogonalProjectionOnto (clockDerivative.adjoint u) :=
  ObservableProjectedDivergence.divergence_source_value _ _ clockDerivative_dense intrinsicClock_dense u

theorem intrinsic_source_divergence_value (u : sourceDerivative.adjoint.domain) :
    intrinsicSource.adjoint ⟨(u : FieldSpace), source_source_divergence_mem u⟩ =
      IntrinsicSpace.orthogonalProjectionOnto (sourceDerivative.adjoint u) :=
  ObservableProjectedDivergence.divergence_source_value _ _ sourceDerivative_dense intrinsicSource_dense u

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicOperators
