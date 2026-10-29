import Foundation.FourCubeNegativeCompletion
import Foundation.FourCubeMovingOddAction

/-! Exact group-word transport of the native72-face cell into the standard box.
All32 interior links remain free. No chart or Gaussian approximation is used. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeNativeTransport
open QuaternionSU2Representation OneSidedBlockIncidence OneSidedBlockRank
open OneSidedCapComplex OneSidedSourceRows FourCubeHaarParity
open FourCubePinnedCoercivity FourCubeDirichletBox

def liftVertex (v : WideVertex) : BoxVertex := fun j => ⟨(v j).val+1,by omega⟩
def liftEdge (e : WideEdge) : BoxEdge := (liftVertex e.1,e.2)
def nativeFace (p : FullFace) : BoxFace := (liftVertex (faceData p).1,(faceData p).2)
def nativeFaces : Finset BoxFace := Finset.univ.image nativeFace

def pull (b : Fin 3 → SU2) (s : InteriorState) (e : FullEdge) : SU2 :=
  link b s (liftEdge (embedEdge e))
def boundary (b : Fin 3 → SU2) (c : Boundary) : SU2 := pull b 1 (.inr c)
def nativeAction (b : Fin 3 → SU2) (s : InteriorState) : ℝ :=
  ∑ p∈nativeFaces,defect (word b s p)

attribute [local irreducible] faces nativeFaces edges innerFaces upperFaces sourceFaces

theorem liftVertex_injective : Function.Injective liftVertex := by
  intro v w h
  funext j
  apply Fin.ext
  have hj := congrArg (fun v : BoxVertex => (v j).val) h
  dsimp [liftVertex] at hj
  omega

theorem liftEdge_injective : Function.Injective liftEdge := by
  intro e f h
  exact Prod.ext (liftVertex_injective (congrArg (fun e : BoxEdge => e.1) h))
    (congrArg (fun e : BoxEdge => e.2) h)

theorem nativeFace_injective : Function.Injective nativeFace := by
  intro p q h
  apply embedFace_bijective.injective
  apply Subtype.ext
  change faceData p=faceData q
  exact Prod.ext (liftVertex_injective (congrArg (fun p : BoxFace => p.1) h))
    (congrArg (fun p : BoxFace => p.2) h)

theorem nativeFace_mem (p : FullFace) : nativeFace p∈faces := by
  have h := faceData_mem p
  simp only [sourceFaces,Finset.mem_filter,Finset.mem_univ,true_and] at h
  have small (j : Fin 4) : ((faceData p).1 j).val<2 := by
    cases p with
    | inl p => exact (p.val.1 j).isLt
    | inr p => exact (p.val.1.1 j).isLt
  simp only [faces,Finset.mem_filter,Finset.mem_univ,true_and,nativeFace,liftVertex]
  refine ⟨h.1,?_,?_⟩
  · change ((faceData p).1 (faceData p).2.1).val+1<3
    have hh := small (faceData p).2.1
    omega
  · change ((faceData p).1 (faceData p).2.2).val+1<3
    have hh := small (faceData p).2.2
    omega

private theorem step_coordinate (x : Fin 3) (hx : x.val<2) :
    ((if x=0 then 1 else 2 : Fin 3).val+1)=(x.val+2)%4 := by
  fin_cases x <;> norm_num at *

theorem lift_shift (v : WideVertex) (hv : ∀ j,(v j).val<2) (j : Fin 4) :
    liftVertex (wideShift v j)=step (liftVertex v) j := by
  funext k
  apply Fin.ext
  by_cases hk : k=j
  · subst k
    simpa only [liftVertex,wideShift,step,Function.update_self,Nat.add_assoc] using
      step_coordinate (v j) (hv j)
  · simp [liftVertex,wideShift,step,hk]

theorem wide_edges (p : FullFace) (t : Fin 4) :
    liftEdge (wideEdges (embedFace p) t)=faceEdges (nativeFace p) t := by
  have small (j : Fin 4) : ((faceData p).1 j).val<2 := by
    cases p with
    | inl p => exact (p.val.1 j).isLt
    | inr p => exact (p.val.1.1 j).isLt
  fin_cases t
  · rfl
  · exact congrArg (fun v => (v,(faceData p).2.2)) (lift_shift _ small _)
  · exact congrArg (fun v => (v,(faceData p).2.1)) (lift_shift _ small _)
  · rfl

theorem translated_rows (p : FullFace) (t : Fin 4) :
    liftEdge (embedEdge (rowEdges p t))=
      faceEdges (nativeFace p) (if flipped p then t.rev else t) := by
  rw [row_geometry,wide_edges]

theorem native_faces_card : nativeFaces.card=72 := by
  classical
  rw [nativeFaces,Finset.card_image_of_injective _ nativeFace_injective]
  simp only [Finset.card_univ,Fintype.card_sum,OneSidedBlockRank.inner_card,
    OneSidedBlockRank.upper_card]

theorem native_faces_subset : nativeFaces ⊆ faces := by
  intro p hp
  rw [nativeFaces] at hp
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hp
  exact nativeFace_mem q

theorem pull_interior (b : Fin 3 → SU2) (s : InteriorState) (e : Interior) :
    pull b s (.inl e)=s e := by
  exact link_interior b s e

private theorem boundary_not_core (c : Boundary) :
    ¬∃ i : Interior,embed i.val=liftEdge (embedEdge (.inr c)) := by
  rintro ⟨i,hi⟩
  have he : liftEdge (embedEdge (.inl i))=liftEdge (embedEdge (.inr c)) := hi
  have hh := embedEdge_injective (liftEdge_injective he)
  cases hh

theorem pull_boundary (b : Fin 3 → SU2) (s : InteriorState) (c : Boundary) :
    pull b s (.inr c)=boundary b c := by
  let e := liftEdge (embedEdge (.inr c))
  have hn : ¬(candidate e∈edges ∧ embed (candidate e)=e) := by
    rintro ⟨hc,he⟩
    exact boundary_not_core c ⟨⟨candidate e,hc⟩,he⟩
  simp only [pull,boundary,link,label,show liftEdge (embedEdge (.inr c))=e from rfl,
    dif_neg hn]
  split_ifs <;> rfl

theorem pull_eq_fill (b : Fin 3 → SU2) (s : InteriorState) :
    pull b s=FourCubeIntegratedCubic.fill (boundary b) s := by
  funext e
  cases e with
  | inl i => exact pull_interior b s i
  | inr c => exact pull_boundary b s c

private theorem reverse_defect (A B C D : SU2) :
    defect (D*C*B⁻¹*A⁻¹)=defect (A*B*C⁻¹*D⁻¹) := by
  have h : D*C*B⁻¹*A⁻¹=(A*B*C⁻¹*D⁻¹)⁻¹ := by group
  rw [h,defect_inv]

theorem native_defect (b : Fin 3 → SU2) (s : InteriorState) (p : FullFace) :
    defect (word b s (nativeFace p))=
      SU2QuaternionOddWord.wordAction (FourCubeMovingOddAction.factors (pull b s) p) := by
  have hl (t : Fin 4) :
      link b s (faceEdges (nativeFace p) (if flipped p then t.rev else t))=
        pull b s (rowEdges p t) := by
    rw [← translated_rows]
    rfl
  change defect (word b s (nativeFace p))=
    defect (pull b s (rowEdges p 0)*pull b s (rowEdges p 1)*
      (pull b s (rowEdges p 2))⁻¹*(pull b s (rowEdges p 3))⁻¹)
  cases hf : flipped p with
  | false =>
    have h0 := hl 0
    have h1 := hl 1
    have h2 := hl 2
    have h3 := hl 3
    simp only [hf,Bool.false_eq_true,ite_false] at h0 h1 h2 h3
    rw [word,h0,h1,h2,h3]
  | true =>
    have h0 := hl 0
    have h1 := hl 1
    have h2 := hl 2
    have h3 := hl 3
    simp only [hf,ite_true] at h0 h1 h2 h3
    change link b s (faceEdges (nativeFace p) 3)=pull b s (rowEdges p 0) at h0
    change link b s (faceEdges (nativeFace p) 2)=pull b s (rowEdges p 1) at h1
    change link b s (faceEdges (nativeFace p) 1)=pull b s (rowEdges p 2) at h2
    change link b s (faceEdges (nativeFace p) 0)=pull b s (rowEdges p 3) at h3
    rw [word,h3,h2,h1,h0]
    exact reverse_defect _ _ _ _

/-- Exact native nonlinear action, with the actual source-only boundary restriction. -/
theorem native_action_identity (b : Fin 3 → SU2) (s : InteriorState) :
    nativeAction b s=FourCubeBoundaryCubic.fullAction
      (FourCubeIntegratedCubic.fill (boundary b) s) := by
  classical
  rw [nativeAction,nativeFaces,Finset.sum_image
    (fun p _ q _ h => nativeFace_injective h)]
  simp_rw [native_defect]
  rw [← FourCubeMovingOddAction.fullAction_rows,pull_eq_fill]

def highBoundary : Boundary := .inl (capHigh FourCubeIntegratedCubic.chosen)
def chordBoundary : Boundary := .inr FourCubeIntegratedCubic.chosen
def lowBoundary : Boundary := .inl (capLow FourCubeIntegratedCubic.chosen)

theorem source_alignment :
    liftEdge (embedEdge (.inr highBoundary))=highSource ∧
    liftEdge (embedEdge (.inr chordBoundary))=chordSource ∧
    liftEdge (embedEdge (.inr lowBoundary))=lowSource := by
  norm_num [highBoundary,chordBoundary,lowBoundary,FourCubeIntegratedCubic.chosen,
    FourCubeIntegratedCubic.chosenEdge,FourCubeIntegratedCubic.base,capHigh,capLow,
    embedEdge,source,direction,OneSidedCapComplex.embedVertex,embedInner,
    liftEdge,liftVertex,shifted,highSource,chordSource,lowSource,funext_iff,
    Fin.forall_fin_succ,Function.update_apply]

theorem boundary_injective :
    Function.Injective (fun c : Boundary => liftEdge (embedEdge (.inr c))) := by
  intro c d h
  exact Sum.inr.inj (embedEdge_injective (liftEdge_injective h))

/-- Explicit restriction to the SAME three source links as the native manuscript cell. -/
theorem boundary_formula (b : Fin 3 → SU2) (c : Boundary) :
    boundary b c=if c=highBoundary then b 0 else
      if c=chordBoundary then b 1 else if c=lowBoundary then b 2 else 1 := by
  let e := liftEdge (embedEdge (.inr c))
  have hn : ¬(candidate e∈edges ∧ embed (candidate e)=e) := by
    rintro ⟨hc,he⟩
    exact boundary_not_core c ⟨⟨candidate e,hc⟩,he⟩
  have hh : e=highSource ↔ c=highBoundary := by
    rw [← source_alignment.1]
    exact boundary_injective.eq_iff
  have hc : e=chordSource ↔ c=chordBoundary := by
    rw [← source_alignment.2.1]
    exact boundary_injective.eq_iff
  have hl : e=lowSource ↔ c=lowBoundary := by
    rw [← source_alignment.2.2]
    exact boundary_injective.eq_iff
  simp only [boundary,pull,link,label,show liftEdge (embedEdge (.inr c))=e from rfl,
    dif_neg hn]
  simp only [hh,hc,hl]
  split_ifs <;> rfl

/-- Source-angle dictionary: no redefinition of the original native boundary law. -/
theorem boundary_angles (x y z : ℝ) :
    boundary ![SU2JointPlaquetteCubic.axis 0 x,(SU2JointPlaquetteCubic.axis 1 y)⁻¹,
      (SU2JointPlaquetteCubic.axis 2 z)⁻¹]=FourCubeIntegratedCubic.boundaryData x y z := by
  funext c
  rw [boundary_formula]
  cases c with
  | inl c =>
    simp only [highBoundary,chordBoundary,lowBoundary,Sum.inl.injEq,
      Sum.inl_ne_inr,ite_false]
    change (if c=capHigh FourCubeIntegratedCubic.chosen then SU2JointPlaquetteCubic.axis 0 x else
      if c=capLow FourCubeIntegratedCubic.chosen then (SU2JointPlaquetteCubic.axis 2 z)⁻¹ else 1)=
      (if c.val=(capHigh FourCubeIntegratedCubic.chosen).val then SU2JointPlaquetteCubic.axis 0 x else
      if c.val=(capLow FourCubeIntegratedCubic.chosen).val then
        (SU2JointPlaquetteCubic.axis 2 z)⁻¹ else 1)
    simp only [Subtype.ext_iff]
  | inr p =>
    simp only [highBoundary,chordBoundary,lowBoundary,Sum.inr.injEq,
      Sum.inr_ne_inl,ite_false]
    change (if p=FourCubeIntegratedCubic.chosen then (SU2JointPlaquetteCubic.axis 1 y)⁻¹ else 1)=
      (if p.val=FourCubeIntegratedCubic.chosen.val then (SU2JointPlaquetteCubic.axis 1 y)⁻¹ else 1)
    simp only [Subtype.ext_iff]

/-- Actual original72-face action equals its embedded standard-box subsum. -/
theorem native_angles (x y z : ℝ) (s : InteriorState) :
    nativeAction ![SU2JointPlaquetteCubic.axis 0 x,(SU2JointPlaquetteCubic.axis 1 y)⁻¹,
      (SU2JointPlaquetteCubic.axis 2 z)⁻¹] s=FourCubeIntegratedCubic.cellAction x y z s := by
  rw [native_action_identity,boundary_angles]
  rfl

theorem native_not_lower (p : FullFace) (e : Interior) (j : Fin 4) :
    nativeFace p≠FourCubeNegativeCompletion.lower e j := by
  intro h
  have hj := congrArg (fun f : BoxFace => (f.1 j).val) h
  simp only [nativeFace,liftVertex,FourCubeNegativeCompletion.lower,Function.update_self] at hj
  omega

theorem native_negative_disjoint : Disjoint nativeFaces FourCubeNegativeCompletion.negativeFaces := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  rw [nativeFaces] at hp
  rw [FourCubeNegativeCompletion.negativeFaces] at hq
  obtain ⟨q,_,hq'⟩ := Finset.mem_image.mp hp
  obtain ⟨⟨e,j⟩,_,he⟩ := Finset.mem_image.mp hq
  exact native_not_lower q e j (hq'.trans he.symm)

def retainedFaces : Finset BoxFace := nativeFaces ∪ FourCubeNegativeCompletion.negativeFaces

def exteriorFaces : Finset BoxFace := faces \ retainedFaces

def exteriorAction (b : Fin 3 → SU2) (s : InteriorState) : ℝ :=
  ∑ p∈exteriorFaces,defect (word b s p)

theorem retained_card : retainedFaces.card=120 := by
  classical
  rw [retainedFaces,Finset.card_union_of_disjoint native_negative_disjoint,
    native_faces_card,FourCubeNegativeCompletion.negative_faces_card]

theorem retained_subset : retainedFaces ⊆ faces :=
  Finset.union_subset native_faces_subset FourCubeNegativeCompletion.negative_faces_subset

theorem exterior_card : exteriorFaces.card=744 := by
  rw [exteriorFaces,Finset.card_sdiff_of_subset retained_subset,face_count,retained_card]

/-- Exact actual partition into native72, negative48 and a744-face remainder.
The remaining source-only cost formula is not assumed by this identity. -/
theorem action_partition (b : Fin 3 → SU2) (s : InteriorState) :
    action b s=FourCubeBoundaryCubic.fullAction (FourCubeIntegratedCubic.fill (boundary b) s)+
      (∑ e : Interior,(FourCubeNegativeCompletion.multiplicity e : ℝ)*defect (s e))+
      exteriorAction b s := by
  classical
  have hh := Finset.sum_sdiff (f := fun p => defect (word b s p)) retained_subset
  rw [retainedFaces,Finset.sum_union native_negative_disjoint] at hh
  change exteriorAction b s+(nativeAction b s+FourCubeNegativeCompletion.negativeAction b s)=
    action b s at hh
  rw [native_action_identity,FourCubeNegativeCompletion.negative_action_identity] at hh
  linarith

end OperatorDerivativeRewrite.Foundation.FourCubeNativeTransport
