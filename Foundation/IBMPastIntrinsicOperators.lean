import Foundation.IBMPastCoreDensity
import Foundation.IBMJointIntrinsicDerivative

/-! Closed dense two-source derivative and its adjoint on each actual IBM past.
The fields retain their native Gaussian source codomain; temporal predictability
and natural-time stochastic integral identification are not asserted. -/
noncomputable section
open Set
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPastIntrinsicOperators
open IBMTimeAveragedObservable IBMPastAverageCore IBMPastCoreDensity
open IBMJointIntrinsicDerivative
set_option backward.isDefEq.respectTransparency false
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

def pastSpace (T : ℝ≥0) : Submodule ℝ IntrinsicSpace :=
  (IBMNaturalFiltrationObstruction.past T).comap IntrinsicSpace.subtype

theorem pastSpace_covers_past (T : ℝ≥0) (f : IBMNaturalFiltrationObstruction.past T) :
    ∃ g : pastSpace T, (g.val : JointL2) = (f : JointL2) :=
  ⟨⟨⟨f.val, past_le_intrinsic T f.property⟩, f.property⟩, rfl⟩

theorem pastSpace_closed (T : ℝ≥0) : IsClosed (pastSpace T : Set IntrinsicSpace) :=
  (IBMNaturalFiltrationObstruction.past_closed T).preimage continuous_subtype_val

local instance (T : ℝ≥0) : CompleteSpace (pastSpace T) :=
  (pastSpace_closed T).completeSpace_coe

def pastDerivative (T : ℝ≥0) : pastSpace T →ₗ.[ℝ] JointFieldSpace :=
  ObservableRestriction.derivative jointDerivative (pastSpace T)

theorem past_domain_iff (T : ℝ≥0) (f : pastSpace T) :
    f ∈ (pastDerivative T).domain ↔ (f.val : JointL2) ∈ pastCore T := by
  change f.val ∈ jointDerivative.domain ↔ _
  rw [joint_domain_iff]
  exact ⟨fun h => ⟨h, f.property⟩, fun h => h.1⟩

theorem pastDerivative_closed (T : ℝ≥0) : (pastDerivative T).IsClosed :=
  ObservableRestriction.derivative_isClosed _ _ jointDerivative_closed

theorem pastDerivative_dense (T : ℝ≥0) :
    Dense ((pastDerivative T).domain : Set (pastSpace T)) := by
  apply (ObservableDensityCriterion.derivative_dense_iff_annihilator_zero
    jointDerivative (pastSpace T)).mpr
  intro g hg
  apply Subtype.ext
  apply Subtype.ext
  apply past_annihilator_zero T (g.val : JointL2) _ g.property
  rw [Submodule.mem_orthogonal']
  intro f hf
  let fi : IntrinsicSpace := ⟨f, ((IBMFiniteAverageCore.mem_intrinsicCore_iff f).mp hf.1).1⟩
  let fp : pastSpace T := ⟨fi, hf.2⟩
  have hp : fp ∈ (pastDerivative T).domain := (past_domain_iff T fp).mpr hf
  exact hg ⟨fp, hp⟩

abbrev pastDivergence (T : ℝ≥0) := (pastDerivative T).adjoint

theorem pastDivergence_closed (T : ℝ≥0) : (pastDivergence T).IsClosed :=
  (pastDerivative T).adjoint_isClosed (pastDerivative_dense T)

/-- Actual Hilbert integration by parts on the maximal adjoint domain.
This is source-valued adjointness, not a temporal Itô identity. -/
theorem integration_by_parts (T : ℝ≥0) (u : (pastDivergence T).domain)
    (f : (pastDerivative T).domain) :
    inner ℝ (pastDivergence T u) (f : pastSpace T) =
      inner ℝ (u : JointFieldSpace) (pastDerivative T f) :=
  (pastDerivative T).adjoint_isFormalAdjoint (pastDerivative_dense T) u f

end OperatorDerivativeRewrite.Foundation.IBMPastIntrinsicOperators
