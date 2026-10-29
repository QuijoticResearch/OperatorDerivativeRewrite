import Foundation.FourCubePinnedCoercivity
import Foundation.OneSidedSourceMatrixData

/-! Actual standard nearest-neighbor Dirichlet box with32 integrated links.
The three exterior sources are arbitrary SU(2) values. All other exterior
links are identity. No root link is pinned and no infinite-volume law is claimed. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeDirichletBox
open QuaternionSU2Representation OneSidedBlockIncidence OneSidedBlockRank
open FourCubeHaarParity FourCubePinnedCoercivity

abbrev BoxVertex := Fin 4 → Fin 4
abbrev BoxEdge := BoxVertex × Fin 4
abbrev BoxFace := BoxVertex × (Fin 4 × Fin 4)

def faces : Finset BoxFace := Finset.univ.filter
  (fun p => p.2.1<p.2.2 ∧ p.1 p.2.1<3 ∧ p.1 p.2.2<3)

def embedVertex (v : Vertex) : BoxVertex := fun j => ⟨(v j).val+1,by omega⟩
def embed (e : EdgeData) : BoxEdge := (embedVertex e.1,e.2)
def step (v : BoxVertex) (j : Fin 4) : BoxVertex :=
  Function.update v j ⟨((v j).val+1)%4,Nat.mod_lt _ (by decide)⟩
def faceEdges (p : BoxFace) : Fin 4 → BoxEdge :=
  ![(p.1,p.2.1),(step p.1 p.2.1,p.2.2),
    (step p.1 p.2.2,p.2.1),(p.1,p.2.2)]

def candidate (e : BoxEdge) : EdgeData :=
  (fun j => ⟨((e.1 j).val+1)%2,Nat.mod_lt _ (by decide)⟩,e.2)

def highSource : BoxEdge := (![2,1,2,2],2)
def chordSource : BoxEdge := (![1,1,3,2],0)
def lowSource : BoxEdge := (![1,1,2,2],2)

/-- Explicit finite lookup, retaining the exact32 existing interior coordinates. -/
def label (e : BoxEdge) : Option (Interior ⊕ Fin 3) :=
  if h : candidate e∈edges ∧ embed (candidate e)=e then some (.inl ⟨candidate e,h.1⟩)
  else if e=highSource then some (.inr 0)
  else if e=chordSource then some (.inr 1)
  else if e=lowSource then some (.inr 2) else none

def link (b : Fin 3 → SU2) (s : InteriorState) (e : BoxEdge) : SU2 :=
  match label e with
  | none => 1
  | some (.inl i) => s i
  | some (.inr j) => b j

def word (b : Fin 3 → SU2) (s : InteriorState) (p : BoxFace) : SU2 :=
  link b s (faceEdges p 0)*link b s (faceEdges p 1)*
    (link b s (faceEdges p 2))⁻¹*(link b s (faceEdges p 3))⁻¹

def action (b : Fin 3 → SU2) (s : InteriorState) : ℝ :=
  ∑ p∈faces,defect (word b s p)

def transverse (a : Fin 4) : Fin 4 := if a=0 then 1 else 0

def isolation (e : Interior) : BoxFace :=
  let a := e.val.2
  let j := transverse a
  let v := if e.val.1 j=0 then Function.update (embedVertex e.val.1) j 0
    else embedVertex e.val.1
  (v,(min a j,max a j))

def slot (e : Interior) : Fin 4 :=
  if e.val.2<transverse e.val.2 then
    if e.val.1 (transverse e.val.2)=0 then 2 else 0
  else if e.val.1 (transverse e.val.2)=0 then 1 else 3

theorem face_count : faces.card=864 := by decide +kernel

attribute [local irreducible] faces

/-- The modulo used to totalize stepping never wraps on an admitted plaquette. -/
theorem face_steps_no_wrap (p : BoxFace) (hp : p∈faces) :
    ((step p.1 p.2.1) p.2.1).val=(p.1 p.2.1).val+1 ∧
      ((step p.1 p.2.2) p.2.2).val=(p.1 p.2.2).val+1 := by
  simp only [faces,Finset.mem_filter,Finset.mem_univ,true_and] at hp
  simp only [step,Function.update_self]
  constructor <;> omega

theorem label_interior (e : Interior) : label (embed e.val)=some (.inl e) := by
  have hc : candidate (embed e.val)=e.val := by
    apply Prod.ext
    · funext j
      apply Fin.ext
      dsimp [candidate,embed,embedVertex]
      have hj := (e.val.1 j).isLt
      omega
    · rfl
  simp [label,hc,e.property]

theorem source_labels : label highSource=some (.inr 0) ∧
    label chordSource=some (.inr 1) ∧ label lowSource=some (.inr 2) := by
  norm_num [label,highSource,chordSource,lowSource,candidate,embed,embedVertex,edges,
    funext_iff,Fin.forall_fin_succ]

theorem isolation_mem : ∀ e : Interior,isolation e∈faces := by decide +kernel

/-- Kernel-checked ordered edge witness: the other three edges are source-free. -/
private theorem isolation_block0 : ∀ i : Fin 8,∀ t : Fin 4,
    label (faceEdges (isolation (OneSidedSourceMatrixData.interiorPoint
      ⟨0+i.val,by omega⟩)) t)=
      if t=slot (OneSidedSourceMatrixData.interiorPoint ⟨0+i.val,by omega⟩) then
        some (.inl (OneSidedSourceMatrixData.interiorPoint ⟨0+i.val,by omega⟩)) else none := by
  intro i
  fin_cases i <;> norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    isolation,slot,transverse,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem isolation_block1 : ∀ i : Fin 8,∀ t : Fin 4,
    label (faceEdges (isolation (OneSidedSourceMatrixData.interiorPoint
      ⟨8+i.val,by omega⟩)) t)=
      if t=slot (OneSidedSourceMatrixData.interiorPoint ⟨8+i.val,by omega⟩) then
        some (.inl (OneSidedSourceMatrixData.interiorPoint ⟨8+i.val,by omega⟩)) else none := by
  intro i
  fin_cases i <;> norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    isolation,slot,transverse,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem isolation_block2 : ∀ i : Fin 8,∀ t : Fin 4,
    label (faceEdges (isolation (OneSidedSourceMatrixData.interiorPoint
      ⟨16+i.val,by omega⟩)) t)=
      if t=slot (OneSidedSourceMatrixData.interiorPoint ⟨16+i.val,by omega⟩) then
        some (.inl (OneSidedSourceMatrixData.interiorPoint ⟨16+i.val,by omega⟩)) else none := by
  intro i
  fin_cases i <;> norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    isolation,slot,transverse,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem isolation_block3 : ∀ i : Fin 8,∀ t : Fin 4,
    label (faceEdges (isolation (OneSidedSourceMatrixData.interiorPoint
      ⟨24+i.val,by omega⟩)) t)=
      if t=slot (OneSidedSourceMatrixData.interiorPoint ⟨24+i.val,by omega⟩) then
        some (.inl (OneSidedSourceMatrixData.interiorPoint ⟨24+i.val,by omega⟩)) else none := by
  intro i
  fin_cases i <;> norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    isolation,slot,transverse,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem isolation_points : ∀ i : Fin 32,∀ t : Fin 4,
    label (faceEdges (isolation (OneSidedSourceMatrixData.interiorPoint i)) t)=
      if t=slot (OneSidedSourceMatrixData.interiorPoint i) then
        some (.inl (OneSidedSourceMatrixData.interiorPoint i)) else none := by
  intro i
  fin_cases i
  · exact isolation_block0 0
  · exact isolation_block0 1
  · exact isolation_block0 2
  · exact isolation_block0 3
  · exact isolation_block0 4
  · exact isolation_block0 5
  · exact isolation_block0 6
  · exact isolation_block0 7
  · exact isolation_block1 0
  · exact isolation_block1 1
  · exact isolation_block1 2
  · exact isolation_block1 3
  · exact isolation_block1 4
  · exact isolation_block1 5
  · exact isolation_block1 6
  · exact isolation_block1 7
  · exact isolation_block2 0
  · exact isolation_block2 1
  · exact isolation_block2 2
  · exact isolation_block2 3
  · exact isolation_block2 4
  · exact isolation_block2 5
  · exact isolation_block2 6
  · exact isolation_block2 7
  · exact isolation_block3 0
  · exact isolation_block3 1
  · exact isolation_block3 2
  · exact isolation_block3 3
  · exact isolation_block3 4
  · exact isolation_block3 5
  · exact isolation_block3 6
  · exact isolation_block3 7

theorem isolation_labels (e : Interior) (t : Fin 4) :
    label (faceEdges (isolation e) t)=if t=slot e then some (.inl e) else none := by
  obtain ⟨i,rfl⟩ := OneSidedSourceMatrixData.interiorPoint_bijective.surjective e
  exact isolation_points i t

attribute [local irreducible] edges

theorem link_interior (b : Fin 3 → SU2) (s : InteriorState) (e : Interior) :
    link b s (embed e.val)=s e := by rw [link,label_interior]

theorem isolation_injective : Function.Injective isolation := by
  intro e f h
  have he := isolation_labels e (slot e)
  have hf := isolation_labels f (slot e)
  rw [h] at he
  rw [he] at hf
  split_ifs at hf with ht
  · exact Sum.inl.inj (Option.some.inj hf)
  · contradiction

private theorem single_word (U : SU2) (k : Fin 4) :
    ((if (0 : Fin 4)=k then U else 1)*(if (1 : Fin 4)=k then U else 1)*
      (if (2 : Fin 4)=k then U else 1)⁻¹*(if (3 : Fin 4)=k then U else 1)⁻¹)=
      if k<2 then U else U⁻¹ := by
  fin_cases k <;> simp

theorem isolation_word (b : Fin 3 → SU2) (s : InteriorState) (e : Interior) :
    word b s (isolation e)=if slot e<2 then s e else (s e)⁻¹ := by
  have hl (t : Fin 4) : link b s (faceEdges (isolation e) t)=
      if t=slot e then s e else 1 := by
    unfold link
    rw [isolation_labels]
    split_ifs <;> rfl
  unfold word
  simp only [hl]
  exact single_word _ _

theorem isolation_defect (b : Fin 3 → SU2) (s : InteriorState) (e : Interior) :
    defect (word b s (isolation e))=defect (s e) := by
  rw [isolation_word]
  split_ifs <;> simp only [defect_inv]

/-- Global coercivity for the ACTUAL864-face Dirichlet action, uniform in all
three source values. Every one of the32 integrated links is controlled. -/
theorem global_coercivity (b : Fin 3 → SU2) (s : InteriorState) :
    (∑ e : Interior,defect (s e)) ≤ action b s := by
  classical
  let chosen : Finset BoxFace := Finset.univ.image isolation
  have hsub : chosen ⊆ faces := by
    intro p hp
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hp
    exact isolation_mem e
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => defect_nonneg (word b s p))
  change (∑ p ∈ Finset.univ.image isolation,defect (word b s p)) ≤ _ at hs
  rw [Finset.sum_image (fun e _ f _ h => isolation_injective h)] at hs
  simpa only [isolation_defect,action] using hs

theorem coordinate_bound (b : Fin 3 → SU2) (s : InteriorState) (e : Interior) :
    defect (s e) ≤ action b s :=
  (Finset.single_le_sum (fun i _ => defect_nonneg (s i)) (Finset.mem_univ e)).trans
    (global_coercivity b s)

theorem action_nonneg (b : Fin 3 → SU2) (s : InteriorState) : 0 ≤ action b s := by
  exact (Finset.sum_nonneg (fun e _ => defect_nonneg (s e))).trans (global_coercivity b s)

end OperatorDerivativeRewrite.Foundation.FourCubeDirichletBox
