import Foundation.ObservableProjectedDivergenceClosure
import Foundation.HilbertAdjointDomainDensity
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The full observable adjoint is the graph closure of projected source
divergence when the source is closed and both derivative domains are dense.
The unclosed domains need not coincide. -/
noncomputable section
open Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ObservableProjectedDivergenceCore
open ObservableRestriction ObservableProjectedDivergence ObservableProjectedDivergenceClosure

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable (A : H →ₗ.[ℝ] E) (V : Submodule ℝ H) [CompleteSpace V]

/-- The sum of two partial operators, retaining both field components. -/
def pairedOperator {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P Q : E →ₗ.[ℝ] F) : PiLp 2 (fun _ : Fin 2 => E) →ₗ.[ℝ] F where
  domain := P.domain.comap (PiLp.projₗ 2 _ 0) ⊓ Q.domain.comap (PiLp.projₗ 2 _ 1)
  toFun := {
    toFun := fun u => P ⟨u.val 0, u.property.1⟩ + Q ⟨u.val 1, u.property.2⟩
    map_add' u v := by
      change P (⟨u.val 0, u.property.1⟩ + ⟨v.val 0, v.property.1⟩) +
        Q (⟨u.val 1, u.property.2⟩ + ⟨v.val 1, v.property.2⟩) = _
      rw [P.map_add, Q.map_add]
      abel
    map_smul' c u := by
      change P (c • ⟨u.val 0, u.property.1⟩) + Q (c • ⟨u.val 1, u.property.2⟩) = _
      rw [P.map_smul, Q.map_smul]
      exact (smul_add c _ _).symm }

/-- Sequential meaning of graph closure in the genuine strong product topology. -/
theorem graph_closure_sequence {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →ₗ.[ℝ] F) (hc : T.IsClosable) (u : E) (v : F)
    (h : (u, v) ∈ T.closure.graph) :
    ∃ f : ℕ → T.domain,
      Tendsto (fun n => (f n : E)) atTop (𝓝 u) ∧
      Tendsto (fun n => T (f n)) atTop (𝓝 v) := by
  have hg : (u, v) ∈ closure (T.graph : Set (E × F)) := by
    rw [← Submodule.topologicalClosure_coe, hc.graph_closure_eq_closure_graph]
    exact h
  obtain ⟨z, hz, ht⟩ := mem_closure_iff_seq_limit.mp hg
  choose f hf1 hf2 using fun n => T.mem_graph_iff.mp (hz n)
  exact ⟨f, ((continuous_fst.tendsto (u, v)).comp ht).congr'
    (Eventually.of_forall fun n => (hf1 n).symm),
    ((continuous_snd.tendsto (u, v)).comp ht).congr'
    (Eventually.of_forall fun n => (hf2 n).symm)⟩

theorem projected_adjoint_eq_restriction
    (hc : A.IsClosed) (hd : Dense (A.domain : Set H)) :
    (projectedOperator A V).adjoint = derivative A V := by
  have ha := HilbertAdjointDomainDensity.closed_adjoint_dense A hc hd
  have hs : Dense ((projectedOperator A V).domain : Set E) := ha
  have hb := HilbertAdjointDomainDensity.closed_bidual A hc hd
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    intro z hz
    obtain ⟨f, hf, he⟩ := (projectedOperator A V).adjoint.mem_graph_iff.mp hz
    have hp (u : A.adjoint.domain) :
        inner ℝ ((projectedOperator A V).adjoint f) (u : E) =
          inner ℝ (f.val : H) (A.adjoint u) := by
      have h := (projectedOperator A V).adjoint_isFormalAdjoint hs f u
      change inner ℝ ((projectedOperator A V).adjoint f) (u : E) =
        inner ℝ (f.val : V) (V.orthogonalProjectionOnto (A.adjoint u)) at h
      rw [V.inner_orthogonalProjectionOnto_eq_of_mem_left] at h
      exact h
    have hm : (f.val : H) ∈ A.adjoint.adjoint.domain :=
      (mem_adjoint_domain_iff_representable A.adjoint ha _).mpr ⟨_, hp⟩
    have heq := A.adjoint.adjoint_apply_eq ha ⟨(f.val : H), hm⟩ hp
    have hg : ((f.val : H), (projectedOperator A V).adjoint f) ∈
        A.adjoint.adjoint.graph := by
      rw [← heq]
      exact A.adjoint.adjoint.mem_graph ⟨(f.val : H), hm⟩
    rw [hb] at hg
    have hg' := (derivative_graph A V f.val _).mpr hg
    simpa only [hf, he] using hg'
  · apply LinearPMap.le_of_le_graph
    intro z hz
    obtain ⟨f, hf, he⟩ := (derivative A V).mem_graph_iff.mp hz
    have hp (u : (projectedOperator A V).domain) :
        inner ℝ (derivative A V f) (u : E) =
          inner ℝ (f : V) (projectedOperator A V u) := by
      have h := projected_pairing A V hd u f
      change inner ℝ (projectedSourceDivergence A V u) (f : V) = _ at h
      change inner ℝ (derivative A V f) (u : E) =
        inner ℝ (f : V) (projectedSourceDivergence A V u)
      simpa only [real_inner_comm] using h.symm
    have hm := (mem_adjoint_domain_iff_representable (projectedOperator A V) hs _).mpr ⟨_, hp⟩
    refine (projectedOperator A V).adjoint.mem_graph_iff.mpr ⟨⟨f.val, hm⟩, hf, ?_⟩
    exact ((projectedOperator A V).adjoint_apply_eq hs ⟨f.val, hm⟩ hp).trans he

theorem projected_closure_eq_adjoint
    (hc : A.IsClosed) (hd : Dense (A.domain : Set H))
    (hv : Dense ((derivative A V).domain : Set V)) :
    (projectedOperator A V).closure = (derivative A V).adjoint := by
  have hs : Dense ((projectedOperator A V).domain : Set E) :=
    HilbertAdjointDomainDensity.closed_adjoint_dense A hc hd
  have hb := HilbertAdjointDomainDensity.closable_bidual (projectedOperator A V)
    (projectedOperator_closable A V hd hv) hs
  rw [projected_adjoint_eq_restriction A V hc hd] at hb
  exact hb.symm

end OperatorDerivativeRewrite.Foundation.ObservableProjectedDivergenceCore
