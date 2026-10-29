import Foundation.FourCubeDirichletBox

/-! Exact negative-side component of the actual Dirichlet action.
This identifies48 nonlinear Wilson terms with their diagonal link penalties;
it does not yet identify the remaining native and exterior-source sums. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeNegativeCompletion
open QuaternionSU2Representation OneSidedBlockIncidence OneSidedBlockRank
open FourCubeHaarParity FourCubePinnedCoercivity FourCubeDirichletBox

def pairs : Finset (Interior × Fin 4) := Finset.univ.filter
  (fun q => q.2≠q.1.val.2 ∧ q.1.val.1 q.2=0)

def lower (e : Interior) (j : Fin 4) : BoxFace :=
  (Function.update (embedVertex e.val.1) j 0,(min e.val.2 j,max e.val.2 j))

def lowerSlot (e : Interior) (j : Fin 4) : Fin 4 := if e.val.2<j then 2 else 1

def negativeFaces : Finset BoxFace := pairs.image (fun q => lower q.1 q.2)

def multiplicity (e : Interior) : ℕ :=
  (Finset.univ.filter (fun j : Fin 4 => j≠e.val.2 ∧ e.val.1 j=0)).card

def negativeAction (b : Fin 3 → SU2) (s : InteriorState) : ℝ :=
  ∑ p∈negativeFaces,defect (word b s p)

theorem pairs_card : pairs.card=48 := by decide +kernel

theorem lower_mem : ∀ e : Interior,∀ j : Fin 4,
    j≠e.val.2 → e.val.1 j=0 → lower e j∈faces := by decide +kernel

private theorem labels_point0 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 0).val.2 → (OneSidedSourceMatrixData.interiorPoint 0).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 0) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 0) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 0)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point1 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 1).val.2 → (OneSidedSourceMatrixData.interiorPoint 1).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 1) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 1) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 1)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point2 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 2).val.2 → (OneSidedSourceMatrixData.interiorPoint 2).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 2) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 2) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 2)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point3 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 3).val.2 → (OneSidedSourceMatrixData.interiorPoint 3).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 3) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 3) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 3)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point4 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 4).val.2 → (OneSidedSourceMatrixData.interiorPoint 4).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 4) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 4) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 4)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point5 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 5).val.2 → (OneSidedSourceMatrixData.interiorPoint 5).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 5) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 5) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 5)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point6 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 6).val.2 → (OneSidedSourceMatrixData.interiorPoint 6).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 6) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 6) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 6)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point7 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 7).val.2 → (OneSidedSourceMatrixData.interiorPoint 7).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 7) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 7) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 7)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point8 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 8).val.2 → (OneSidedSourceMatrixData.interiorPoint 8).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 8) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 8) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 8)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point9 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 9).val.2 → (OneSidedSourceMatrixData.interiorPoint 9).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 9) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 9) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 9)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point10 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 10).val.2 → (OneSidedSourceMatrixData.interiorPoint 10).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 10) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 10) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 10)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point11 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 11).val.2 → (OneSidedSourceMatrixData.interiorPoint 11).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 11) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 11) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 11)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point12 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 12).val.2 → (OneSidedSourceMatrixData.interiorPoint 12).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 12) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 12) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 12)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point13 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 13).val.2 → (OneSidedSourceMatrixData.interiorPoint 13).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 13) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 13) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 13)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point14 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 14).val.2 → (OneSidedSourceMatrixData.interiorPoint 14).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 14) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 14) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 14)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point15 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 15).val.2 → (OneSidedSourceMatrixData.interiorPoint 15).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 15) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 15) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 15)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point16 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 16).val.2 → (OneSidedSourceMatrixData.interiorPoint 16).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 16) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 16) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 16)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point17 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 17).val.2 → (OneSidedSourceMatrixData.interiorPoint 17).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 17) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 17) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 17)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point18 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 18).val.2 → (OneSidedSourceMatrixData.interiorPoint 18).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 18) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 18) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 18)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point19 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 19).val.2 → (OneSidedSourceMatrixData.interiorPoint 19).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 19) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 19) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 19)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point20 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 20).val.2 → (OneSidedSourceMatrixData.interiorPoint 20).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 20) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 20) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 20)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point21 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 21).val.2 → (OneSidedSourceMatrixData.interiorPoint 21).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 21) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 21) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 21)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point22 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 22).val.2 → (OneSidedSourceMatrixData.interiorPoint 22).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 22) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 22) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 22)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point23 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 23).val.2 → (OneSidedSourceMatrixData.interiorPoint 23).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 23) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 23) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 23)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point24 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 24).val.2 → (OneSidedSourceMatrixData.interiorPoint 24).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 24) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 24) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 24)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point25 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 25).val.2 → (OneSidedSourceMatrixData.interiorPoint 25).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 25) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 25) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 25)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point26 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 26).val.2 → (OneSidedSourceMatrixData.interiorPoint 26).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 26) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 26) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 26)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point27 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 27).val.2 → (OneSidedSourceMatrixData.interiorPoint 27).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 27) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 27) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 27)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point28 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 28).val.2 → (OneSidedSourceMatrixData.interiorPoint 28).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 28) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 28) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 28)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point29 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 29).val.2 → (OneSidedSourceMatrixData.interiorPoint 29).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 29) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 29) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 29)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point30 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 30).val.2 → (OneSidedSourceMatrixData.interiorPoint 30).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 30) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 30) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 30)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem labels_point31 : ∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint 31).val.2 → (OneSidedSourceMatrixData.interiorPoint 31).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint 31) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint 31) j then some (.inl (OneSidedSourceMatrixData.interiorPoint 31)) else none := by
  norm_num [OneSidedSourceMatrixData.interiorPoint,label,faceEdges,
    lower,lowerSlot,candidate,embed,embedVertex,step,edges,
    highSource,chordSource,lowSource,funext_iff,Fin.forall_fin_succ,Function.update_apply]

private theorem point_labels : ∀ i : Fin 32,∀ j : Fin 4,
    j≠(OneSidedSourceMatrixData.interiorPoint i).val.2 →
      (OneSidedSourceMatrixData.interiorPoint i).val.1 j=0 → ∀ t : Fin 4,
      label (faceEdges (lower (OneSidedSourceMatrixData.interiorPoint i) j) t)=
        if t=lowerSlot (OneSidedSourceMatrixData.interiorPoint i) j then
          some (.inl (OneSidedSourceMatrixData.interiorPoint i)) else none := by
  intro i
  fin_cases i
  · exact labels_point0
  · exact labels_point1
  · exact labels_point2
  · exact labels_point3
  · exact labels_point4
  · exact labels_point5
  · exact labels_point6
  · exact labels_point7
  · exact labels_point8
  · exact labels_point9
  · exact labels_point10
  · exact labels_point11
  · exact labels_point12
  · exact labels_point13
  · exact labels_point14
  · exact labels_point15
  · exact labels_point16
  · exact labels_point17
  · exact labels_point18
  · exact labels_point19
  · exact labels_point20
  · exact labels_point21
  · exact labels_point22
  · exact labels_point23
  · exact labels_point24
  · exact labels_point25
  · exact labels_point26
  · exact labels_point27
  · exact labels_point28
  · exact labels_point29
  · exact labels_point30
  · exact labels_point31

theorem lower_labels (e : Interior) (j : Fin 4) (hj : j≠e.val.2)
    (hv : e.val.1 j=0) (t : Fin 4) :
    label (faceEdges (lower e j) t)=if t=lowerSlot e j then some (.inl e) else none := by
  obtain ⟨i,rfl⟩ := OneSidedSourceMatrixData.interiorPoint_bijective.surjective e
  exact point_labels i j hj hv t

attribute [local irreducible] faces edges pairs negativeFaces

theorem lower_defect (b : Fin 3 → SU2) (s : InteriorState) (e : Interior)
    (j : Fin 4) (hj : j≠e.val.2) (hv : e.val.1 j=0) :
    defect (word b s (lower e j))=defect (s e) := by
  have hl (t : Fin 4) : link b s (faceEdges (lower e j) t)=
      if t=lowerSlot e j then s e else 1 := by
    unfold link
    rw [lower_labels e j hj hv]
    split_ifs <;> rfl
  unfold word
  simp only [hl]
  by_cases h : e.val.2<j <;> simp [lowerSlot,h,defect_inv]

theorem lower_injective : Set.InjOn (fun q : Interior × Fin 4 => lower q.1 q.2) pairs := by
  intro p hp q hq h
  have hp' : p.2≠p.1.val.2 ∧ p.1.val.1 p.2=0 := by simpa [pairs] using hp
  have hq' : q.2≠q.1.val.2 ∧ q.1.val.1 q.2=0 := by simpa [pairs] using hq
  have he := lower_labels p.1 p.2 hp'.1 hp'.2 (lowerSlot p.1 p.2)
  have hf := lower_labels q.1 q.2 hq'.1 hq'.2 (lowerSlot p.1 p.2)
  change lower p.1 p.2=lower q.1 q.2 at h
  rw [h] at he
  rw [he] at hf
  have hh : p.1=q.1 := by
    split_ifs at hf
    · exact Sum.inl.inj (Option.some.inj hf)
    · contradiction
  apply Prod.ext hh
  have ha := congrArg (fun f : BoxFace => f.2) h
  dsimp only [lower] at ha
  rw [hh] at ha
  simp only [min_def,max_def] at ha
  split_ifs at ha <;> simp_all only [Prod.mk.injEq]

theorem negative_faces_card : negativeFaces.card=48 := by
  classical
  rw [negativeFaces,Finset.card_image_of_injOn lower_injective,pairs_card]

theorem negative_faces_subset : negativeFaces ⊆ faces := by
  intro p hp
  rw [negativeFaces] at hp
  obtain ⟨⟨e,j⟩,hq,rfl⟩ := Finset.mem_image.mp hp
  have h : j≠e.val.2 ∧ e.val.1 j=0 := by simpa [pairs] using hq
  exact lower_mem e j h.1 h.2

/-- Exact nonlinear diagonal completion, for arbitrary exterior source values. -/
theorem negative_action_identity (b : Fin 3 → SU2) (s : InteriorState) :
    negativeAction b s=∑ e : Interior,(multiplicity e : ℝ)*defect (s e) := by
  classical
  unfold negativeAction negativeFaces
  rw [Finset.sum_image lower_injective]
  have he : (∑ q∈pairs,defect (word b s (lower q.1 q.2)))=
      ∑ q∈pairs,defect (s q.1) := by
    apply Finset.sum_congr rfl
    intro q hq
    have h : q.2≠q.1.val.2 ∧ q.1.val.1 q.2=0 := by simpa [pairs] using hq
    exact lower_defect b s q.1 q.2 h.1 h.2
  rw [he,pairs,Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.sum_filter]
  simp [multiplicity]

theorem negative_action_le (b : Fin 3 → SU2) (s : InteriorState) :
    negativeAction b s ≤ action b s := by
  unfold negativeAction action
  exact Finset.sum_le_sum_of_subset_of_nonneg negative_faces_subset
    (fun p _ _ => defect_nonneg (word b s p))

theorem pole_multiplicity : multiplicity OneSidedPinnedInterior.pole=3 := by decide +kernel

/-- A link with no negative-side plaquette; it still belongs to the native cell. -/
def topEdge : Interior := ⟨(![0,1,1,1],0),by norm_num [edges]⟩

theorem top_multiplicity : multiplicity topEdge=0 := by decide +kernel

def spike (U : SU2) : InteriorState := fun e => if e=topEdge then U else 1

theorem negative_spike_zero (b : Fin 3 → SU2) (U : SU2) :
    negativeAction b (spike U)=0 := by
  classical
  rw [negative_action_identity]
  apply Finset.sum_eq_zero
  intro e he
  by_cases h : e=topEdge
  · simp [spike,h,top_multiplicity]
  · simp [spike,h,defect_one]

/-- Sharp scope obstruction: the negative-side component alone cannot control all links. -/
theorem negative_spike_no_control (b : Fin 3 → SU2) (U : SU2) (hU : U≠1) :
    ¬defect (spike U topEdge) ≤ negativeAction b (spike U) := by
  rw [negative_spike_zero]
  have he : spike U topEdge=U := by simp [spike]
  rw [he]
  intro h
  exact hU ((defect_zero_iff U).mp (le_antisymm h (defect_nonneg U)))

end OperatorDerivativeRewrite.Foundation.FourCubeNegativeCompletion
