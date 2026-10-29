import Foundation.FourCubeIntegratedResponse

/-! Exact one-link conditional action of the existing full72-face cell.
All other31 retained links are fixed1; no full marginal identity is assumed. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeConditionalAction
open QuaternionSU2Representation SU2JointPlaquetteCubic
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex FourCubeChordIncidence
open FourCubeHaarParity FourCubeHaarChannels FourCubeIntegratedCubic
attribute [local irreducible] edges upperFaces

def singleState (U : SU2) (e : Interior) : SU2 := if e.val=chosenEdge.val then U else 1

theorem core_single (U : SU2) (e : EdgeData) :
    coreField (singleState U) e=if e=chosenEdge.val then U else 1 := by
  by_cases he : e∈edges
  · simp [coreField,singleState,he]
  · have hn : e≠chosenEdge.val := by intro h; rw [h] at he; exact he chosenEdge.property
    simp [coreField,he,hn]

private theorem face_single (U : SU2) (p : FaceData) (hp : p∈innerFaces) :
    FourCubeWilsonCubic.faceAction (coreField (singleState U)) p=
      if chosenEdge.val∈boundary p then 1-halfTrace U else 0 := by
  rw [innerFaces_eq] at hp
  simp only [faceList,List.toFinset_cons,List.toFinset_nil,Finset.mem_insert,
    Finset.notMem_empty,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [FourCubeWilsonCubic.faceAction,core_single,faceEdge,chosenEdge,
    FourCubeIntegratedCubic.base,shifted,boundary,SU2WilsonConvolution.halfTrace_inv,
    FourCubeWilsonCubic.trace_one,funext_iff,Fin.forall_fin_succ,Fin.exists_fin_succ,Function.update_apply]

theorem internal_single (U : SU2) : internalAction (singleState U)=3*(1-halfTrace U) := by
  unfold internalAction FourCubeWilsonCubic.innerAction
  rw [Finset.sum_congr rfl (fun p hp => face_single U p hp),← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  rw [edge_degree chosenEdge.val chosenEdge.property]
  norm_num

def high : Vertex × Fin 4 := (capHigh chosen).val
def low : Vertex × Fin 4 := (capLow chosen).val

abbrev highTouch (p : EdgeData × Fin 4) : Prop :=
  (shifted p.1.1 p.1.2,p.2)=high ∨ (p.1.1,p.2)=high

abbrev lowTouch (p : EdgeData × Fin 4) : Prop :=
  (shifted p.1.1 p.1.2,p.2)=low ∨ (p.1.1,p.2)=low

def capClass (p : EdgeData × Fin 4) : Fin 4 :=
  if p=chosen.val then 0 else if highTouch p then 1 else if lowTouch p then 2 else 3

private theorem zero_fiber : upperFaces.filter (fun p => capClass p=0)={chosen.val} := by
  ext p
  simp only [Finset.mem_filter,Finset.mem_singleton]
  by_cases he : p=chosen.val
  · subst p
    simp [capClass,chosen.property]
  · simp only [capClass,if_neg he]
    split_ifs <;> simp [he]

private theorem high_fiber : upperFaces.filter (fun p => capClass p=1)=
    {((shifted FourCubeIntegratedCubic.base 0,1),2),((![1,0,1,0],3),2)} := by
  ext ⟨⟨v,d⟩,j⟩
  simp only [Finset.mem_filter,upperFaces,edges,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton]
  revert d j
  fin_cases v <;> decide

private theorem low_fiber : upperFaces.filter (fun p => capClass p=2)=
    {((FourCubeIntegratedCubic.base,1),2),((![0,0,1,0],3),2)} := by
  ext ⟨⟨v,d⟩,j⟩
  simp only [Finset.mem_filter,upperFaces,edges,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton]
  revert d j
  fin_cases v <;> decide

theorem capClass_count : ∀ i : Fin 4,
    (upperFaces.filter (fun p => capClass p=i)).card=(![1,2,2,43] : Fin 4 → ℕ) i := by
  have h0 : (upperFaces.filter (fun p => capClass p=0)).card=1 := by rw [zero_fiber]; simp
  have h1 : (upperFaces.filter (fun p => capClass p=1)).card=2 := by
    rw [high_fiber]
    norm_num [FourCubeIntegratedCubic.base,shifted,funext_iff,Fin.forall_fin_succ]
  have h2 : (upperFaces.filter (fun p => capClass p=2)).card=2 := by
    rw [low_fiber]
    norm_num [FourCubeIntegratedCubic.base,funext_iff,Fin.forall_fin_succ]
  have ht := Finset.sum_fiberwise upperFaces capClass (fun _ => (1:ℕ))
  simp only [Finset.sum_const,Nat.nsmul_eq_mul,mul_one,upperFaces_card] at ht
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · change (upperFaces.filter (fun p => capClass p=3)).card=43
    rw [Fin.sum_univ_four,h0,h1,h2] at ht
    omega

private theorem touches_disjoint : ∀ p∈upperFaces, p≠chosen.val → ¬ (highTouch p ∧ lowTouch p) := by
  intro p hp hn
  rcases p with ⟨⟨v,d⟩,j⟩
  simp only [upperFaces,edges,Finset.mem_filter,Finset.mem_univ,true_and] at hp
  revert d j
  fin_cases v <;> decide

def traceValues (x y z : ℝ) : Fin 4 → ℝ :=
  ![halfTrace (axis 0 x*axis 1 y*axis 2 z),Real.cos x,Real.cos z,1]

private theorem trace_class (x y z : ℝ) (p : Upper) :
    halfTrace (word (boundaryData x y z) p)=traceValues x y z (capClass p.val) := by
  by_cases he : p=chosen
  · subst p
    simp [capClass,traceValues,word_chosen]
  · have hv : p.val≠chosen.val := fun h => he (Subtype.ext h)
    have hd := touches_disjoint p.val p.property hv
    have hc : (shifted p.val.1.1 p.val.1.2,p.val.2)≠(p.val.1.1,p.val.2) := by
      intro h
      exact FourCubeBoundaryCubic.ribbon_caps_distinct p (Subtype.ext h)
    have hu : boundaryData x y z (.inr p)=1 := by simp [boundaryData,hv]
    unfold word
    rw [hu,inv_one,mul_one]
    change halfTrace ((if (shifted p.val.1.1 p.val.1.2,p.val.2)=high then axis 0 x else
        if (shifted p.val.1.1 p.val.1.2,p.val.2)=low then (axis 2 z)⁻¹ else 1)*
      (if (p.val.1.1,p.val.2)=high then axis 0 x else
        if (p.val.1.1,p.val.2)=low then (axis 2 z)⁻¹ else 1)⁻¹)=_
    by_cases h1 : (shifted p.val.1.1 p.val.1.2,p.val.2)=high <;>
      by_cases h2 : (p.val.1.1,p.val.2)=high <;>
      by_cases h3 : (shifted p.val.1.1 p.val.1.2,p.val.2)=low <;>
      by_cases h4 : (p.val.1.1,p.val.2)=low
    all_goals simp_all [capClass,highTouch,lowTouch,traceValues,FourCubeWilsonCubic.axis_trace,
      SU2WilsonConvolution.halfTrace_inv,FourCubeWilsonCubic.trace_one]

theorem ribbonSum_one (x y z : ℝ) : ribbonSum (boundaryData x y z) (singleState 1)=
    halfTrace (axis 0 x*axis 1 y*axis 2 z)+2*Real.cos x+2*Real.cos z+43 := by
  unfold ribbonSum ribbonChannel linkProbe
  simp only [singleState,ite_self,mul_one]
  simp_rw [trace_class]
  rw [Finset.sum_coe_sort upperFaces (fun p => traceValues x y z (capClass p))]
  rw [← Finset.sum_fiberwise' upperFaces capClass (traceValues x y z)]
  simp only [Finset.sum_const,capClass_count,nsmul_eq_mul]
  norm_num [Fin.sum_univ_succ,traceValues] <;> ring

theorem ribbonSum_change (x y z : ℝ) (U : SU2) :
    ribbonSum (boundaryData x y z) (singleState U)-ribbonSum (boundaryData x y z) (singleState 1)=
      halfTrace (U*(axis 0 x*axis 1 y*axis 2 z))-halfTrace (axis 0 x*axis 1 y*axis 2 z)+halfTrace U-1 := by
  let d := fun p : Upper => ribbonChannel (boundaryData x y z) p (singleState U)-
    ribbonChannel (boundaryData x y z) p (singleState 1)
  have hs : (∑ p : Upper,d p)=∑ p∈({chosen,partner} : Finset Upper),d p := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    have he : ribbonInterior p≠chosenEdge := by
      intro he
      rcases (edge_fiber p).mp he with he | he
      · subst p; simp at hp
      · subst p; simp at hp
    have hv : (ribbonInterior p).val≠chosenEdge.val := fun h => he (Subtype.ext h)
    simp [d,ribbonChannel,linkProbe,singleState,hv,he]
  rw [Finset.sum_pair chosen_ne_partner] at hs
  dsimp only [d] at hs
  rw [Finset.sum_sub_distrib] at hs
  unfold ribbonSum
  have ht : halfTrace ((axis 0 x*axis 1 y*axis 2 z)*U)=
      halfTrace (U*(axis 0 x*axis 1 y*axis 2 z)) := SU2WilsonConvolution.halfTrace_mul_comm _ _
  simp [ribbonChannel,linkProbe,singleState,chosen_edge,partner_edge,word_chosen,
    word_partner,FourCubeWilsonCubic.trace_one,ht] at hs ⊢ <;> linarith

/-- EXACT full72-face action with precisely one retained link left free. -/
theorem conditional_action (x y z : ℝ) (U : SU2) : cellAction x y z (singleState U)=
    5-4*halfTrace U-halfTrace (U*(axis 0 x*axis 1 y*axis 2 z))+
      2*(1-Real.cos x)+2*(1-Real.cos z) := by
  unfold cellAction
  rw [action_decomposition,internal_single]
  have h1 := ribbonSum_one x y z
  have h2 := ribbonSum_change x y z U
  linarith

end OperatorDerivativeRewrite.Foundation.FourCubeConditionalAction
