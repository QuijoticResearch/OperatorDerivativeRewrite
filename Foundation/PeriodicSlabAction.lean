import Foundation.PeriodicWilsonSlab

/-! Exact cyclic action accounting for the actual periodic four-dimensional field. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicSlabAction
open PeriodicTemporalSlab QuaternionSU2Representation

attribute [local irreducible] PeriodicWilsonSlab.spatialAction PeriodicWilsonSlab.temporalAction

private abbrev Pair4 := {ij : Fin 4 × Fin 4 // ij.1 < ij.2}
private abbrev Pair3 := {ij : Fin 3 × Fin 3 // ij.1 < ij.2}

private def pairSplit : Pair4 ≃ Pair3 ⊕ Fin 3 where
  toFun p := if h : p.val.2.val < 3 then
    .inl ⟨(⟨p.val.1.val,by omega⟩,⟨p.val.2.val,h⟩),p.property⟩
    else .inr ⟨p.val.1.val,by have := p.property; omega⟩
  invFun p := match p with
    | .inl q => ⟨(q.val.1.castSucc,q.val.2.castSucc),q.property⟩
    | .inr i => ⟨(i.castSucc,Fin.last 3),i.castSucc_lt_last⟩
  left_inv p := by
    dsimp
    split_ifs with h
    · rfl
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp only [Fin.val_last]
        omega
  right_inv p := by
    cases p with
    | inl q => simp only [Fin.val_castSucc,q.val.2.isLt,dite_true]
    | inr i => simp only [Fin.val_last,lt_self_iff_false,dite_false]; rfl

private def vertexSplit : PeriodicInteriorGaugeKernel.Vertex ≃ ZMod 4 × SpatialVertex where
  toFun v := (v (Fin.last 3),fun i => v i.castSucc)
  invFun p := embed p.2 p.1
  left_inv v := by
    funext k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · exact embed_time _ _
    · exact embed_spatial _ _ _
  right_inv p := by
    apply Prod.ext
    · exact embed_time p.2 p.1
    · funext i; exact embed_spatial _ _ _

private theorem pairSplit_spatial (p : Pair3) :
    pairSplit.symm (.inl p)=⟨(p.val.1.castSucc,p.val.2.castSucc),p.property⟩ := rfl

private theorem pairSplit_temporal (i : Fin 3) :
    pairSplit.symm (.inr i)=⟨(i.castSucc,Fin.last 3),i.castSucc_lt_last⟩ := rfl

private def faceProduct : PeriodicInteriorGaugeKernel.Face ≃
    PeriodicInteriorGaugeKernel.Vertex × Pair4 where
  toFun p := (p.val.1,⟨p.val.2,p.property⟩)
  invFun p := ⟨(p.1,p.2.val),p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def spatialFaceProduct : SpatialFace ≃ SpatialVertex × Pair3 where
  toFun p := (p.val.1,⟨p.val.2,p.property⟩)
  invFun p := ⟨(p.1,p.2.val),p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem full_action (L : PeriodicSU2FlatHolonomy.Links) :
    PeriodicSU2FlatHolonomy.action L=
      ∑ t : ZMod 4,(PeriodicWilsonSlab.spatialAction (spatialField L t)+
        PeriodicWilsonSlab.temporalAction (spatialField L t) (spatialField L (t+1))
          (temporalField L t)) := by
  unfold PeriodicSU2FlatHolonomy.action
  rw [← faceProduct.symm.sum_comp]
  simp only [Fintype.sum_prod_type,faceProduct,Equiv.coe_fn_symm_mk]
  rw [← vertexSplit.symm.sum_comp]
  simp only [Fintype.sum_prod_type,vertexSplit,Equiv.coe_fn_symm_mk]
  apply Finset.sum_congr rfl
  intro t _
  conv_lhs =>
    arg 2
    ext v
    rw [← pairSplit.symm.sum_comp]
    simp only [Fintype.sum_sum_type,pairSplit_spatial,pairSplit_temporal]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (·+·)
  · unfold PeriodicWilsonSlab.spatialAction
    rw [← spatialFaceProduct.symm.sum_comp]
    simp only [Fintype.sum_prod_type,spatialFaceProduct,Equiv.coe_fn_symm_mk]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro p _
    rw [spatial_word L t ⟨(v,p.val),p.property⟩]
  · unfold PeriodicWilsonSlab.temporalAction
    simp only [SpatialEdge,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro i _
    rw [temporal_word L t (v,i)]

theorem cyclic_half_action (L : PeriodicSU2FlatHolonomy.Links) :
    PeriodicSU2FlatHolonomy.action L=
      ∑ t : ZMod 4,PeriodicWilsonSlab.halfAction (spatialField L t)
        (spatialField L (t+1)) (temporalField L t) := by
  rw [full_action]
  unfold PeriodicWilsonSlab.halfAction
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_div,← Finset.sum_div]
  have h := Equiv.sum_comp (Equiv.addRight (1 : ZMod 4))
    (fun t => PeriodicWilsonSlab.spatialAction (spatialField L t))
  change (∑ t : ZMod 4,PeriodicWilsonSlab.spatialAction (spatialField L (t+1)))=_ at h
  rw [h]
  ring

end OperatorDerivativeRewrite.Foundation.PeriodicSlabAction
