import Foundation.IBMPastIntrinsicOperators
import Foundation.IBMIntrinsicDivergenceClosure

/-! The maximal actual-past adjoint is the strong graph closure of genuine
native source-divergence pairs after projection to that past. -/
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPastDivergenceClosure
open IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMIntrinsicDivergenceClosure IBMPastIntrinsicOperators
open ObservableProjectedDivergence ObservableProjectedDivergenceClosure
open ObservableProjectedDivergenceCore
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.ibmValue IBMConstructedSources.clockPath
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
local instance (T : ℝ≥0) : CompleteSpace (pastSpace T) :=
  (pastSpace_closed T).completeSpace_coe

def projectedFull (T : ℝ≥0) : JointFieldSpace →ₗ.[ℝ] pastSpace T :=
  projectedOperator jointDerivative (pastSpace T)

theorem projectedFull_closable (T : ℝ≥0) : (projectedFull T).IsClosable :=
  projectedOperator_closable _ _ jointDerivative_dense (pastDerivative_dense T)

theorem projectedFull_closure (T : ℝ≥0) :
    (projectedFull T).closure = pastDivergence T :=
  projected_closure_eq_adjoint _ _ jointDerivative_closed jointDerivative_dense
    (pastDerivative_dense T)

theorem full_domain_mem (T : ℝ≥0) (u : jointDivergence.domain) :
    (u : JointFieldSpace) ∈ (pastDivergence T).domain :=
  source_divergence_mem _ _ jointDerivative_dense (pastDerivative_dense T) u

theorem full_domain_value (T : ℝ≥0) (u : jointDivergence.domain) :
    pastDivergence T ⟨u.val, full_domain_mem T u⟩ =
      (pastSpace T).orthogonalProjectionOnto (jointDivergence u) :=
  divergence_source_value _ _ jointDerivative_dense (pastDerivative_dense T) u

def nativePair (T : ℝ≥0) : JointFieldSpace →ₗ.[ℝ] pastSpace T where
  domain := ambientPairOperator.domain
  toFun := {
    toFun := fun u => (pastSpace T).orthogonalProjectionOnto (ambientPairOperator u)
    map_add' u v := by rw [ambientPairOperator.map_add, map_add]
    map_smul' c u := by rw [ambientPairOperator.map_smul, map_smul]; rfl }

theorem nativePair_formal (T : ℝ≥0) : (nativePair T).IsFormalAdjoint (pastDerivative T) := by
  intro u f
  change inner ℝ ((pastSpace T).orthogonalProjectionOnto (ambientPairOperator u))
    (f.val : pastSpace T) = _
  rw [(pastSpace T).inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact ambientPairOperator_formal u ⟨f.val.val, f.property⟩

theorem nativePair_le (T : ℝ≥0) : nativePair T ≤ pastDivergence T :=
  (nativePair_formal T).symm.le_adjoint (pastDerivative_dense T)

set_option maxHeartbeats 800000 in
-- Elaborating the actual nested source/past adjoint spaces exceeds the default budget.
theorem nativePair_closable (T : ℝ≥0) : (nativePair T).IsClosable :=
  (pastDivergence_closed T).isClosable.leIsClosable (nativePair_le T)

set_option maxHeartbeats 800000 in
-- Actual source-domain sequence witnesses retain the nested past projection types.
theorem projectedFull_le_native_closure (T : ℝ≥0) :
    projectedFull T ≤ (nativePair T).closure := by
  apply LinearPMap.le_of_le_graph
  intro z hz
  obtain ⟨u, hu, hv⟩ := (projectedFull T).mem_graph_iff.mp hz
  obtain ⟨a, b, ha, hb⟩ := full_graph_approximation u
  have ht := ((pastSpace T).orthogonalProjectionOnto.continuous.tendsto
    (jointDivergence u)).comp hb
  have hg : ((u : JointFieldSpace),
      (pastSpace T).orthogonalProjectionOnto (jointDivergence u)) ∈
        (nativePair T).closure.graph := by
    apply (nativePair_closable T).closure_isClosed.mem_of_tendsto (ha.prodMk_nhds ht)
    apply Eventually.of_forall
    intro n
    apply LinearPMap.le_graph_of_le (nativePair T).le_closure
    refine (nativePair T).mem_graph_iff.mpr ⟨⟨_, pair_mem (a n) (b n)⟩, rfl, ?_⟩
    change (pastSpace T).orthogonalProjectionOnto
      (ambientPairOperator ⟨pairField (a n) (b n), pair_mem (a n) (b n)⟩) = _
    rw [pair_value]
    rfl
  change (u : JointFieldSpace) = z.1 at hu
  change (pastSpace T).orthogonalProjectionOnto (jointDivergence u) = z.2 at hv
  simpa only [hu, hv] using hg

set_option maxHeartbeats 800000 in
-- Closure comparison instantiates both actual native-source and past-domain graphs.
theorem nativePair_closure (T : ℝ≥0) : (nativePair T).closure = pastDivergence T := by
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    rw [← (nativePair_closable T).graph_closure_eq_closure_graph]
    exact (Submodule.topologicalClosure_mono
      (LinearPMap.le_graph_of_le (nativePair_le T))).trans
        (pastDivergence_closed T).submodule_topologicalClosure_eq.le
  · rw [← projectedFull_closure T]
    apply LinearPMap.le_of_le_graph
    rw [← (projectedFull_closable T).graph_closure_eq_closure_graph]
    exact (Submodule.topologicalClosure_mono
      (LinearPMap.le_graph_of_le (projectedFull_le_native_closure T))).trans
        (nativePair_closable T).closure_isClosed.submodule_topologicalClosure_eq.le

set_option maxHeartbeats 800000 in
-- Instantiating graph sequences on the actual source L2 domains needs this local budget.
/-- Strong field convergence AND convergence of the past-projected sum.
No separate unprojected source-divergence limit is required. -/
theorem full_native_graph_approximation (T : ℝ≥0) (u : (pastDivergence T).domain) :
    ∃ (a : ℕ → sourceDerivative.adjoint.domain) (b : ℕ → clockDerivative.adjoint.domain),
      Tendsto (fun n => pairField (a n) (b n)) atTop (𝓝 (u : JointFieldSpace)) ∧
      Tendsto (fun n => (pastSpace T).orthogonalProjectionOnto
        (IntrinsicSpace.orthogonalProjectionOnto
          (sourceDerivative.adjoint (a n) + clockDerivative.adjoint (b n))))
        atTop (𝓝 (pastDivergence T u)) := by
  have hg : ((u : JointFieldSpace), pastDivergence T u) ∈ (nativePair T).closure.graph := by
    rw [nativePair_closure]
    exact (pastDivergence T).mem_graph u
  obtain ⟨w, hw1, hw2⟩ := graph_closure_sequence (nativePair T)
    (nativePair_closable T) _ _ hg
  let a (n : ℕ) : sourceDerivative.adjoint.domain := ⟨(w n).val 0, (w n).property.1⟩
  let b (n : ℕ) : clockDerivative.adjoint.domain := ⟨(w n).val 1, (w n).property.2⟩
  have hp (n : ℕ) : pairField (a n) (b n) = (w n).val := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  have hv (n : ℕ) : (pastSpace T).orthogonalProjectionOnto
      (IntrinsicSpace.orthogonalProjectionOnto
        (sourceDerivative.adjoint (a n) + clockDerivative.adjoint (b n))) =
        nativePair T (w n) := by
    change (pastSpace T).orthogonalProjectionOnto _ =
      (pastSpace T).orthogonalProjectionOnto
        (IntrinsicSpace.orthogonalProjectionOnto (sourceDerivative.adjoint (a n)) +
          IntrinsicSpace.orthogonalProjectionOnto (clockDerivative.adjoint (b n)))
    rw [← map_add]
  exact ⟨a, b, hw1.congr' (Eventually.of_forall fun n => (hp n).symm),
    hw2.congr' (Eventually.of_forall fun n => (hv n).symm)⟩

end OperatorDerivativeRewrite.Foundation.IBMPastDivergenceClosure
