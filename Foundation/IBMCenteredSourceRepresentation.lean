import Foundation.IBMGlobalVacuum

/-! Every centered actual IBM L2 observable has an explicit native pair of
source-divergence preimages. This static representation is not predictable. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCenteredSourceRepresentation
open InfiniteGaussian IBMTimeAveragedObservable IBMFiniteAverageCore IBMIntrinsicOperators
open IBMJointIntrinsicDerivative IBMNativeSourceRecovery IBMGlobalVacuum
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

def intrinsicOne : IntrinsicSpace := ⟨one, one_intrinsic⟩

def recoveryPair (f : JointL2) : JointFieldSpace :=
  pairField (sourceRecovery f) (clockRecovery (sourceVacuum f))

theorem partial_one_graph :
    (BochnerClosedOperator.tensor gaussianProduct gaussianOne gaussianOne, (0 : FieldSpace)) ∈
      partialDerivative.graph := by
  rw [BochnerClosedOperator.mem_lift_graph_iff]
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct gaussianOne gaussianOne,
    Lp.coeFn_zero GaussianVectorL2 2 gaussianProduct] with x ht hz
  rw [ht, hz]
  exact closedDerivative_constant_graph (gaussianOne x)

theorem source_one_graph : (one, (0 : FieldSpace)) ∈ sourceDerivative.graph := by
  change (one, (0 : FieldSpace)) ∈
    (AdjointUnitaryTransport.pullback sourceUnitary partialDerivative).graph
  rw [AdjointUnitaryTransport.mem_pullback_graph, source_one]
  exact partial_one_graph

theorem clock_one_graph : (one, (0 : FieldSpace)) ∈ clockDerivative.graph := by
  change (one, (0 : FieldSpace)) ∈
    (AdjointUnitaryTransport.pullback clockUnitary partialDerivative).graph
  rw [AdjointUnitaryTransport.mem_pullback_graph, clock_one]
  exact partial_one_graph

theorem joint_one_graph : (intrinsicOne, (0 : JointFieldSpace)) ∈ jointDerivative.graph := by
  rw [joint_graph_iff]
  exact ⟨(ObservableRestriction.derivative_graph _ _ intrinsicOne 0).mpr source_one_graph,
    (ObservableRestriction.derivative_graph _ _ intrinsicOne 0).mpr clock_one_graph⟩

theorem divergence_mean_zero (u : jointDivergence.domain) :
    (∫ ω, (jointDivergence u : JointL2) ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  have ho := LinearPMap.mem_domain_of_mem_graph joint_one_graph
  have he := (jointDerivative.image_iff ho).mpr joint_one_graph
  have h := jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense u ⟨intrinsicOne, ho⟩
  rw [← he, inner_zero_right] at h
  rw [← one_inner_mean]
  change inner ℝ (intrinsicOne : IntrinsicSpace) (jointDivergence u) = 0
  simpa only [real_inner_comm] using h

set_option maxHeartbeats 800000 in
-- The native pair membership witnesses elaborate large source-adjoint types.
theorem centered_reconstruction (f : IntrinsicSpace) :
    ∃ h : recoveryPair f ∈ jointDivergence.domain,
      jointDivergence ⟨recoveryPair f, h⟩ =
        f - (∫ ω, (f : JointL2) ω ∂IBMSourceLaws.jointMeasure) • intrinsicOne := by
  obtain ⟨h, hv⟩ := ordered_intrinsic_reconstruction (f : JointL2)
  refine ⟨h, hv.trans ?_⟩
  rw [composed_vacuum_expectation, map_sub, map_smul]
  have hf := IntrinsicSpace.orthogonalProjectionOnto_mem_subspace_eq_self f
  have h1 := IntrinsicSpace.orthogonalProjectionOnto_mem_subspace_eq_self intrinsicOne
  change IntrinsicSpace.orthogonalProjectionOnto one = intrinsicOne at h1
  rw [hf, h1]

theorem centered_surjective (f : IntrinsicSpace)
    (hf : (∫ ω, (f : JointL2) ω ∂IBMSourceLaws.jointMeasure) = 0) :
    ∃ u : jointDivergence.domain, jointDivergence u = f := by
  obtain ⟨h, hv⟩ := centered_reconstruction f
  exact ⟨⟨_, h⟩, by simpa only [hf, zero_smul, sub_zero] using hv⟩

theorem range_iff_centered (f : IntrinsicSpace) :
    (∃ u : jointDivergence.domain, jointDivergence u = f) ↔
      (∫ ω, (f : JointL2) ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact divergence_mean_zero u
  · exact centered_surjective f

theorem source_vacuum_norm (f : JointL2) : ‖sourceVacuum f‖ ≤ ‖f‖ := by
  have h : ‖(GaussianNumberSectors.projection 0).compLpL 2 gaussianProduct
      (sourceUnitary f)‖ ≤ (1 : ℝ) * ‖sourceUnitary f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(GaussianNumberSectors.projection 0).coeFn_compLpL (sourceUnitary f)]
      with x hx
    rw [hx, one_mul]
    exact GaussianNumberSectors.projection_norm_le 0 _
  simpa only [sourceVacuum, LinearIsometryEquiv.norm_map, one_mul] using h

theorem recovery_pair_bound_sq (f : JointL2) : ‖recoveryPair f‖ ^ 2 ≤ 2 * ‖f‖ ^ 2 := by
  have ha := source_recovery_norm f
  have hb := (clock_recovery_norm (sourceVacuum f)).trans (source_vacuum_norm f)
  have hsum : ‖recoveryPair f‖ ^ 2 =
      ‖sourceRecovery f‖ ^ 2 + ‖clockRecovery (sourceVacuum f)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [recoveryPair, pairField, PiLp.inner_apply, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, real_inner_self_eq_norm_sq]
  rw [hsum]
  nlinarith [norm_nonneg (sourceRecovery f), norm_nonneg (clockRecovery (sourceVacuum f)),
    norm_nonneg f]

theorem recovery_pair_add (f g : JointL2) :
    recoveryPair (f + g) = recoveryPair f + recoveryPair g := by
  apply PiLp.ext
  intro i
  fin_cases i
  · exact sourceRecovery.map_add f g
  · change clockRecovery (sourceVacuum (f + g)) =
      clockRecovery (sourceVacuum f) + clockRecovery (sourceVacuum g)
    simp only [sourceVacuum, map_add]

theorem recovery_pair_smul (c : ℝ) (f : JointL2) :
    recoveryPair (c • f) = c • recoveryPair f := by
  apply PiLp.ext
  intro i
  fin_cases i
  · exact sourceRecovery.map_smul c f
  · change clockRecovery (sourceVacuum (c • f)) = c • clockRecovery (sourceVacuum f)
    simp only [sourceVacuum, map_smul]

/-- An explicit continuous linear reconstruction map. The sharper verified
squared estimate is two; the constructor uses the convenient bound two. -/
def recoveryOperator : JointL2 →L[ℝ] JointFieldSpace :=
  ({ toFun := recoveryPair, map_add' := recovery_pair_add, map_smul' := recovery_pair_smul } :
    JointL2 →ₗ[ℝ] JointFieldSpace).mkContinuous 2 (fun f => by
      change ‖recoveryPair f‖ ≤ 2 * ‖f‖
      have h := recovery_pair_bound_sq f
      nlinarith [norm_nonneg (recoveryPair f), norm_nonneg f])

end OperatorDerivativeRewrite.Foundation.IBMCenteredSourceRepresentation
