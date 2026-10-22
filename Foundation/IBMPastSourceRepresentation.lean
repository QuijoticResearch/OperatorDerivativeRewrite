import Foundation.IBMPastDivergenceClosure
import Foundation.IBMCenteredSourceRepresentation

/-! Bounded native source reconstruction of actual IBM past observables.
This is static source-valued reconstruction, not a temporal predictable formula. -/
noncomputable section
open MeasureTheory Set
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPastSourceRepresentation
open IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMIntrinsicDivergenceClosure IBMPastIntrinsicOperators IBMPastDivergenceClosure
open IBMCenteredSourceRepresentation IBMNativeSourceRecovery IBMGlobalVacuum
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.ibmValue IBMConstructedSources.clockPath
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
local instance (T : ℝ≥0) : CompleteSpace (pastSpace T) :=
  (pastSpace_closed T).completeSpace_coe

theorem one_mem_past (T : ℝ≥0) : intrinsicOne ∈ pastSpace T := by
  change AEStronglyMeasurable[IBMNaturalFiltrationObstruction.naturalFiltration T]
    (one : JointL2) IBMSourceLaws.jointMeasure
  exact aestronglyMeasurable_const.congr one_coeFn.symm

def pastOne (T : ℝ≥0) : pastSpace T := ⟨intrinsicOne, one_mem_past T⟩

theorem past_one_graph (T : ℝ≥0) :
    (pastOne T, (0 : JointFieldSpace)) ∈ (pastDerivative T).graph :=
  (ObservableRestriction.derivative_graph _ _ _ _).mpr joint_one_graph

theorem recovery_native_mem (T : ℝ≥0) (f : JointL2) :
    recoveryPair f ∈ (nativePair T).domain :=
  ⟨LinearPMap.mem_domain_of_mem_graph (source_recovery_graph f),
    LinearPMap.mem_domain_of_mem_graph (clock_recovery_graph (sourceVacuum f))⟩

theorem native_centered_reconstruction (T : ℝ≥0) (f : pastSpace T) :
    nativePair T ⟨recoveryPair (f.val : JointL2), recovery_native_mem T (f.val : JointL2)⟩ =
      f - (∫ ω, (f.val : JointL2) ω ∂IBMSourceLaws.jointMeasure) • pastOne T := by
  obtain ⟨h, hv⟩ := centered_reconstruction f.val
  have hg : (recoveryPair (f.val : JointL2),
      ambientPairOperator ⟨_, recovery_native_mem T (f.val : JointL2)⟩) ∈
        jointDivergence.graph :=
    LinearPMap.le_graph_of_le
      (ambientPairOperator_formal.symm.le_adjoint jointDerivative_dense)
      (ambientPairOperator.mem_graph ⟨_, recovery_native_mem T (f.val : JointL2)⟩)
  have he := (jointDivergence.image_iff h).mpr hg
  change (pastSpace T).orthogonalProjectionOnto
    (ambientPairOperator ⟨_, recovery_native_mem T (f.val : JointL2)⟩) = _
  rw [he, hv, map_sub, map_smul]
  have hf := (pastSpace T).orthogonalProjectionOnto_mem_subspace_eq_self f
  have h1 := (pastSpace T).orthogonalProjectionOnto_mem_subspace_eq_self (pastOne T)
  change (pastSpace T).orthogonalProjectionOnto intrinsicOne = pastOne T at h1
  rw [hf, h1]

theorem past_centered_reconstruction (T : ℝ≥0) (f : pastSpace T) :
    ∃ h : recoveryPair (f.val : JointL2) ∈ (pastDivergence T).domain,
      pastDivergence T ⟨_, h⟩ =
        f - (∫ ω, (f.val : JointL2) ω ∂IBMSourceLaws.jointMeasure) • pastOne T := by
  have hg := LinearPMap.le_graph_of_le (nativePair_le T)
    ((nativePair T).mem_graph ⟨_, recovery_native_mem T (f.val : JointL2)⟩)
  rw [native_centered_reconstruction] at hg
  have h := LinearPMap.mem_domain_of_mem_graph hg
  exact ⟨h, ((pastDivergence T).image_iff h).mpr hg |>.symm⟩

theorem divergence_mean_zero (T : ℝ≥0) (u : (pastDivergence T).domain) :
    (∫ ω, ((pastDivergence T u).val : JointL2) ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  have hd := LinearPMap.mem_domain_of_mem_graph (past_one_graph T)
  have he := ((pastDerivative T).image_iff hd).mpr (past_one_graph T)
  have h := integration_by_parts T u ⟨pastOne T, hd⟩
  rw [← he, inner_zero_right] at h
  rw [← one_inner_mean]
  change inner ℝ (pastOne T) (pastDivergence T u) = 0
  simpa only [real_inner_comm] using h

theorem range_iff_centered (T : ℝ≥0) (f : pastSpace T) :
    (∃ u : (pastDivergence T).domain, pastDivergence T u = f) ↔
      (∫ ω, (f.val : JointL2) ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact divergence_mean_zero T u
  · intro hf
    obtain ⟨h, hv⟩ := past_centered_reconstruction T f
    exact ⟨⟨_, h⟩, by simpa only [hf, zero_smul, sub_zero] using hv⟩

def recoveryOnPast (T : ℝ≥0) : pastSpace T →L[ℝ] JointFieldSpace :=
  recoveryOperator.comp (IntrinsicSpace.subtypeL.comp (pastSpace T).subtypeL)

theorem recovery_bound_sq (T : ℝ≥0) (f : pastSpace T) :
    ‖recoveryOnPast T f‖ ^ 2 ≤ 2 * ‖f‖ ^ 2 :=
  recovery_pair_bound_sq (f.val : JointL2)

end OperatorDerivativeRewrite.Foundation.IBMPastSourceRepresentation
