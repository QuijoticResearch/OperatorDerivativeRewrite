import Foundation.AdjointBidual

/-! Adjoint-domain density and automatic bidual identities from genuine Hilbert closability. -/
noncomputable section
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.HilbertAdjointDomainDensity
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem closed_adjoint_dense (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : Dense (T.adjoint.domain : Set F) := by
  have ho : T.adjoint.domain.orthogonal = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro y hy
    change y=0
    let G : Submodule ℝ (WithLp 2 (E × F)) :=
      T.graph.comap (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap
    have hG : IsClosed (G : Set (WithLp 2 (E × F))) :=
      hT.preimage (WithLp.prod_continuous_ofLp 2 E F)
    have hGG : G.orthogonal.orthogonal=G := by
      rw [G.orthogonal_orthogonal_eq_closure, hG.submodule_topologicalClosure_eq]
    have hm : WithLp.toLp 2 ((0:E),y) ∈ G.orthogonal.orthogonal := by
      intro w hw
      have hg : ((WithLp.ofLp w).2, -(WithLp.ofLp w).1) ∈ T.adjoint.graph := by
        rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd, Submodule.mem_adjoint_iff]
        intro a b hab
        have hh := hw (WithLp.toLp 2 (a,b)) hab
        simp only [WithLp.prod_inner_apply] at hh
        simp only [inner_neg_right, sub_neg_eq_add]
        linarith
      have hz : (WithLp.ofLp w).2 ∈ T.adjoint.domain :=
        LinearPMap.mem_domain_iff.mpr ⟨-(WithLp.ofLp w).1, hg⟩
      simpa only [WithLp.prod_inner_apply, inner_zero_right, zero_add] using
        hy (WithLp.ofLp w).2 hz
    rw [hGG] at hm
    have hp : ((0:E),y) ∈ T.graph := hm
    exact T.graph_fst_eq_zero_snd hp rfl
  have ht : T.adjoint.domain.topologicalClosure=⊤ :=
    T.adjoint.domain.topologicalClosure_eq_top_iff.mpr ho
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, ht]
  rfl

theorem closable_adjoint_dense (T : E →ₗ.[ℝ] F) (hT : T.IsClosable)
    (hd : Dense (T.domain : Set E)) : Dense (T.adjoint.domain : Set F) := by
  have h := closed_adjoint_dense T.closure hT.closure_isClosed (operatorClosure_dense_domain hd)
  rw [operatorClosure_adjoint_eq hT hd] at h
  exact h

theorem closable_of_adjoint_dense (T : E →ₗ.[ℝ] F)
    (hd : Dense (T.domain : Set E)) (ha : Dense (T.adjoint.domain : Set F)) : T.IsClosable :=
  (T.adjoint.adjoint_isClosed ha).isClosable.leIsClosable
    ((T.adjoint_isFormalAdjoint hd).le_adjoint ha)

theorem closable_iff_adjoint_dense (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E)) :
    T.IsClosable ↔ Dense (T.adjoint.domain : Set F) :=
  ⟨fun h => closable_adjoint_dense T h hd, closable_of_adjoint_dense T hd⟩

theorem closed_bidual (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : T.adjoint.adjoint=T :=
  closedOperator_adjoint_adjoint_eq hT hd (closed_adjoint_dense T hT hd)

theorem closable_bidual (T : E →ₗ.[ℝ] F) (hT : T.IsClosable)
    (hd : Dense (T.domain : Set E)) : T.adjoint.adjoint=T.closure :=
  closableOperator_adjoint_adjoint_eq_closure hT hd (closable_adjoint_dense T hT hd)

end OperatorDerivativeRewrite.Foundation.HilbertAdjointDomainDensity
