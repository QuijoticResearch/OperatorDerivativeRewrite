import Foundation.IBMJointIntrinsicDerivative
import Foundation.ObservableProjectedDivergenceCore

/-! Full intrinsic IBM divergence as the graph closure of the projected sum
of genuine scenery and clock source divergences. No unclosed-domain equality. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicDivergenceClosure
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open ObservableProjectedDivergenceClosure ObservableProjectedDivergenceCore
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

def ambientPairOperator : JointFieldSpace →ₗ.[ℝ] IntrinsicSpace :=
  pairedOperator (projectedOperator sourceDerivative IntrinsicSpace)
    (projectedOperator clockDerivative IntrinsicSpace)

theorem pair_mem (a : sourceDerivative.adjoint.domain) (b : clockDerivative.adjoint.domain) :
    pairField a b ∈ ambientPairOperator.domain := ⟨a.property, b.property⟩

theorem pair_value (a : sourceDerivative.adjoint.domain) (b : clockDerivative.adjoint.domain) :
    ambientPairOperator ⟨pairField a b, pair_mem a b⟩ =
      IntrinsicSpace.orthogonalProjectionOnto
        (sourceDerivative.adjoint a + clockDerivative.adjoint b) := by
  exact (map_add IntrinsicSpace.orthogonalProjectionOnto _ _).symm

theorem ambientPairOperator_dense : Dense (ambientPairOperator.domain : Set JointFieldSpace) := by
  have hs := HilbertAdjointDomainDensity.closed_adjoint_dense _
    sourceDerivative_closed sourceDerivative_dense
  have hc := HilbertAdjointDomainDensity.closed_adjoint_dense _
    clockDerivative_closed clockDerivative_dense
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  simp only [Submodule.mem_orthogonal']
  intro g hg
  have h0 : g 0 = 0 := hs.eq_zero_of_inner_left ℝ (by
    intro a ha
    have h := hg (pairField a 0) (pair_mem ⟨a, ha⟩ 0)
    simpa [pairField, PiLp.inner_apply, Fin.sum_univ_two] using h)
  have h1 : g 1 = 0 := hc.eq_zero_of_inner_left ℝ (by
    intro b hb
    have h := hg (pairField 0 b) (pair_mem 0 ⟨b, hb⟩)
    simpa [pairField, PiLp.inner_apply, Fin.sum_univ_two] using h)
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1

theorem ambientPairOperator_formal : ambientPairOperator.IsFormalAdjoint jointDerivative := by
  intro u f
  have h := ambient_pair_duality ⟨u.val 0, u.property.1⟩ ⟨u.val 1, u.property.2⟩ f
  have hp : pairField (u.val 0) (u.val 1) = (u : JointFieldSpace) := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  have ht := h.trans (congrArg (fun v : JointFieldSpace => inner ℝ v (jointDerivative f)) hp)
  change inner ℝ
    (IntrinsicSpace.orthogonalProjectionOnto (sourceDerivative.adjoint ⟨u.val 0, u.property.1⟩) +
      IntrinsicSpace.orthogonalProjectionOnto (clockDerivative.adjoint ⟨u.val 1, u.property.2⟩))
    (f : IntrinsicSpace) = _
  rw [← map_add]
  exact ht

set_option maxHeartbeats 800000 in
-- The actual source-space adjoint terms need a larger local elaboration budget.
theorem ambientPairOperator_adjoint : ambientPairOperator.adjoint = jointDerivative := by
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    intro z hz
    obtain ⟨f, hf, he⟩ := ambientPairOperator.adjoint.mem_graph_iff.mp hz
    let k := ambientPairOperator.adjoint f
    have hs (a : (projectedOperator sourceDerivative IntrinsicSpace).domain) :
        inner ℝ (k 0) (a : FieldSpace) =
          inner ℝ (f : IntrinsicSpace) (projectedOperator sourceDerivative IntrinsicSpace a) := by
      have h := ambientPairOperator.adjoint_isFormalAdjoint ambientPairOperator_dense f
        ⟨pairField a 0, pair_mem a 0⟩
      change inner ℝ k (pairField a 0) = inner ℝ (f : IntrinsicSpace)
        (projectedOperator sourceDerivative IntrinsicSpace a +
          projectedOperator clockDerivative IntrinsicSpace 0) at h
      rw [(projectedOperator clockDerivative IntrinsicSpace).map_zero, add_zero] at h
      simpa only [pairField, PiLp.inner_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, inner_zero_right, add_zero] using h
    have hc (b : (projectedOperator clockDerivative IntrinsicSpace).domain) :
        inner ℝ (k 1) (b : FieldSpace) =
          inner ℝ (f : IntrinsicSpace) (projectedOperator clockDerivative IntrinsicSpace b) := by
      have h := ambientPairOperator.adjoint_isFormalAdjoint ambientPairOperator_dense f
        ⟨pairField 0 b, pair_mem 0 b⟩
      change inner ℝ k (pairField 0 b) = inner ℝ (f : IntrinsicSpace)
        (projectedOperator sourceDerivative IntrinsicSpace 0 +
          projectedOperator clockDerivative IntrinsicSpace b) at h
      rw [(projectedOperator sourceDerivative IntrinsicSpace).map_zero, zero_add] at h
      simpa only [pairField, PiLp.inner_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, inner_zero_right, zero_add] using h
    have gs : (f.val, k 0) ∈ (projectedOperator sourceDerivative IntrinsicSpace).adjoint.graph := by
      have hd := HilbertAdjointDomainDensity.closed_adjoint_dense _
        sourceDerivative_closed sourceDerivative_dense
      have hm := (mem_adjoint_domain_iff_representable
        (projectedOperator sourceDerivative IntrinsicSpace) hd f.val).mpr ⟨k 0, hs⟩
      exact ((projectedOperator sourceDerivative IntrinsicSpace).adjoint.image_iff hm).mp
        ((projectedOperator sourceDerivative IntrinsicSpace).adjoint_apply_eq
          hd ⟨f.val, hm⟩ hs).symm
    have gc : (f.val, k 1) ∈ (projectedOperator clockDerivative IntrinsicSpace).adjoint.graph := by
      have hd := HilbertAdjointDomainDensity.closed_adjoint_dense _
        clockDerivative_closed clockDerivative_dense
      have hm := (mem_adjoint_domain_iff_representable
        (projectedOperator clockDerivative IntrinsicSpace) hd f.val).mpr ⟨k 1, hc⟩
      exact ((projectedOperator clockDerivative IntrinsicSpace).adjoint.image_iff hm).mp
        ((projectedOperator clockDerivative IntrinsicSpace).adjoint_apply_eq
          hd ⟨f.val, hm⟩ hc).symm
    rw [projected_adjoint_eq_restriction _ _ sourceDerivative_closed sourceDerivative_dense] at gs
    rw [projected_adjoint_eq_restriction _ _ clockDerivative_closed clockDerivative_dense] at gc
    have hg := (joint_graph_iff f.val k).mpr ⟨gs, gc⟩
    simpa only [k, hf, he] using hg
  · exact ambientPairOperator_formal.le_adjoint ambientPairOperator_dense

theorem ambientPairOperator_closable : ambientPairOperator.IsClosable :=
  (jointDerivative.adjoint_isClosed jointDerivative_dense).isClosable.leIsClosable
    (ambientPairOperator_formal.symm.le_adjoint jointDerivative_dense)

theorem full_intrinsic_divergence_closure : ambientPairOperator.closure = jointDivergence := by
  have h := HilbertAdjointDomainDensity.closable_bidual ambientPairOperator
    ambientPairOperator_closable ambientPairOperator_dense
  rw [ambientPairOperator_adjoint] at h
  exact h.symm

set_option maxHeartbeats 800000 in
-- Instantiating graph sequences on the actual source L2 spaces is expensive.
/-- Every natural intrinsic integrand is a strong joint graph limit of genuine
ambient source integrands. Only the projected SUM must converge. -/
theorem full_graph_approximation (u : jointDivergence.domain) :
    ∃ (a : ℕ → sourceDerivative.adjoint.domain) (b : ℕ → clockDerivative.adjoint.domain),
      Tendsto (fun n => pairField (a n) (b n)) atTop (𝓝 (u : JointFieldSpace)) ∧
      Tendsto (fun n => IntrinsicSpace.orthogonalProjectionOnto
        (sourceDerivative.adjoint (a n) + clockDerivative.adjoint (b n)))
        atTop (𝓝 (jointDivergence u)) := by
  have hg : ((u : JointFieldSpace), jointDivergence u) ∈ ambientPairOperator.closure.graph := by
    rw [full_intrinsic_divergence_closure]
    exact jointDivergence.mem_graph u
  obtain ⟨w, hw1, hw2⟩ := graph_closure_sequence ambientPairOperator
    ambientPairOperator_closable _ _ hg
  let a (n : ℕ) : sourceDerivative.adjoint.domain := ⟨(w n).val 0, (w n).property.1⟩
  let b (n : ℕ) : clockDerivative.adjoint.domain := ⟨(w n).val 1, (w n).property.2⟩
  have hp (n : ℕ) : pairField (a n) (b n) = (w n).val := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  have hv (n : ℕ) : IntrinsicSpace.orthogonalProjectionOnto
      (sourceDerivative.adjoint (a n) + clockDerivative.adjoint (b n)) =
        ambientPairOperator (w n) :=
    map_add IntrinsicSpace.orthogonalProjectionOnto _ _
  exact ⟨a, b, hw1.congr' (Eventually.of_forall fun n => (hp n).symm),
    hw2.congr' (Eventually.of_forall fun n => (hv n).symm)⟩

/-- Conversely, these two strong limits force membership in the full natural
intrinsic divergence domain and identify its value. -/
theorem strong_graph_limit
    (a : ℕ → sourceDerivative.adjoint.domain) (b : ℕ → clockDerivative.adjoint.domain)
    (u : JointFieldSpace) (v : IntrinsicSpace)
    (hu : Tendsto (fun n => pairField (a n) (b n)) atTop (𝓝 u))
    (hv : Tendsto (fun n => IntrinsicSpace.orthogonalProjectionOnto
      (sourceDerivative.adjoint (a n) + clockDerivative.adjoint (b n))) atTop (𝓝 v)) :
    ∃ h : u ∈ jointDivergence.domain, jointDivergence ⟨u, h⟩ = v := by
  have hm : (u, v) ∈ jointDivergence.graph :=
    (jointDerivative.adjoint_isClosed jointDerivative_dense).mem_of_tendsto
      (hu.prodMk_nhds hv) (Eventually.of_forall fun n => by
        obtain ⟨h, he⟩ := ambient_pair_divergence (a n) (b n)
        exact jointDivergence.mem_graph_iff.mpr ⟨⟨_, h⟩, rfl, he⟩)
  have h := LinearPMap.mem_domain_of_mem_graph hm
  exact ⟨h, ((jointDivergence.image_iff h).mpr hm).symm⟩

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicDivergenceClosure
