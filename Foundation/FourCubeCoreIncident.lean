import Foundation.FourCubeNativeTransport

/-! Exhaustive classification of actual plaquettes touching the32 integrated links.
Finite coordinate cardinality plus proved inclusion identifies the retained120 faces. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeCoreIncident
open QuaternionSU2Representation OneSidedBlockIncidence OneSidedBlockRank
open OneSidedCapComplex OneSidedSourceRows FourCubeHaarParity FourCubePinnedCoercivity
open FourCubeDirichletBox FourCubeNativeTransport

def Core (e : BoxEdge) : Prop :=
  (∀ j : Fin 4,0<(e.1 j).val ∧ (e.1 j).val<3) ∧ (e.1 e.2).val=1

instance core_decidable (e : BoxEdge) : Decidable (Core e) :=
  inferInstanceAs (Decidable ((∀ j : Fin 4,0<(e.1 j).val ∧ (e.1 j).val<3) ∧ (e.1 e.2).val=1))

def coreFaces : Finset BoxFace := faces.filter (fun p => ∃ t : Fin 4,Core (faceEdges p t))

theorem core_faces_card : coreFaces.card=120 := by decide +kernel

attribute [local irreducible] faces coreFaces nativeFaces edges innerFaces upperFaces sourceFaces

theorem core_embed (e : Interior) : Core (embed e.val) := by
  constructor
  · intro j
    change 0<(e.val.1 j).val+1 ∧ (e.val.1 j).val+1<3
    have h := (e.val.1 j).isLt
    omega
  · have he : e.val.1 e.val.2=0 := by
      simpa only [edges,Finset.mem_filter,Finset.mem_univ,true_and] using e.property
    change (e.val.1 e.val.2).val+1=1
    rw [he]
    rfl

theorem core_lift_iff (e : WideEdge) : Core (liftEdge e) ↔ wideInterior e := by
  constructor
  · rintro ⟨hv,ha⟩
    refine ⟨?_,?_⟩
    · intro j
      have h := hv j
      change 0<(e.1 j).val+1 ∧ (e.1 j).val+1<3 at h
      omega
    · apply Fin.ext
      change (e.1 e.2).val+1=1 at ha
      omega
  · rintro ⟨hv,ha⟩
    constructor
    · intro j
      change 0<(e.1 j).val+1 ∧ (e.1 j).val+1<3
      have h := hv j
      omega
    · change (e.1 e.2).val+1=1
      rw [ha]
      rfl

/-- Semantic meaning of an interior label, retaining the actual group-field address. -/
theorem label_core_source (e : BoxEdge) (i : Interior) (h : label e=some (.inl i)) :
    embed i.val=e := by
  by_cases hc : candidate e∈edges ∧ embed (candidate e)=e
  · simp only [label,dif_pos hc] at h
    have hi : (⟨candidate e,hc.1⟩ : Interior)=i := Sum.inl.inj (Option.some.inj h)
    rw [← hi]
    exact hc.2
  · simp only [label,dif_neg hc] at h
    split_ifs at h <;> cases h

theorem native_core (p : FullFace) : nativeFace p∈coreFaces := by
  rw [coreFaces]
  apply Finset.mem_filter.mpr
  refine ⟨nativeFace_mem p,?_⟩
  have h := faceData_mem p
  simp only [sourceFaces,Finset.mem_filter,Finset.mem_univ,true_and] at h
  have trans (t : Fin 4) : Core (faceEdges (nativeFace p) t) ↔
      wideInterior (wideEdges (embedFace p) t) := by rw [← wide_edges,core_lift_iff]
  rcases h.2 with h | h | h | h
  · exact ⟨0,(trans 0).mpr h⟩
  · exact ⟨1,(trans 1).mpr h⟩
  · exact ⟨2,(trans 2).mpr h⟩
  · exact ⟨3,(trans 3).mpr h⟩

theorem negative_core (e : Interior) (j : Fin 4) (hj : j≠e.val.2) (hv : e.val.1 j=0) :
    FourCubeNegativeCompletion.lower e j∈coreFaces := by
  rw [coreFaces]
  apply Finset.mem_filter.mpr
  refine ⟨FourCubeNegativeCompletion.lower_mem e j hj hv,?_⟩
  refine ⟨FourCubeNegativeCompletion.lowerSlot e j,?_⟩
  have h := FourCubeNegativeCompletion.lower_labels e j hj hv
    (FourCubeNegativeCompletion.lowerSlot e j)
  rw [if_pos rfl] at h
  have he := label_core_source _ e h
  rw [← he]
  exact core_embed e

theorem retained_core_subset : retainedFaces ⊆ coreFaces := by
  intro p hp
  rw [retainedFaces] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rw [nativeFaces] at hp
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hp
    exact native_core q
  · rw [FourCubeNegativeCompletion.negativeFaces] at hp
    obtain ⟨⟨e,j⟩,hq,rfl⟩ := Finset.mem_image.mp hp
    have h : j≠e.val.2 ∧ e.val.1 j=0 := by simpa [FourCubeNegativeCompletion.pairs] using hq
    exact negative_core e j h.1 h.2

/-- Exhaustiveness follows from actual inclusion and independently checked equal cardinality. -/
theorem retained_eq_core : retainedFaces=coreFaces := by
  apply Finset.eq_of_subset_of_card_le retained_core_subset
  rw [core_faces_card,retained_card]

theorem exterior_no_core (p : BoxFace) (hp : p∈exteriorFaces) (t : Fin 4) :
    ¬Core (faceEdges p t) := by
  rw [exteriorFaces] at hp
  obtain ⟨hf,hn⟩ := Finset.mem_sdiff.mp hp
  intro h
  apply hn
  rw [retained_eq_core,coreFaces]
  exact Finset.mem_filter.mpr ⟨hf,⟨t,h⟩⟩

theorem exterior_no_interior_label (p : BoxFace) (hp : p∈exteriorFaces)
    (t : Fin 4) (i : Interior) : label (faceEdges p t)≠some (.inl i) := by
  intro h
  apply exterior_no_core p hp t
  rw [← label_core_source _ i h]
  exact core_embed i

/-- Pure-coordinate exterior criterion, suitable for finite source-count certificates. -/
theorem exterior_filter : exteriorFaces=faces.filter (fun p => ∀ t : Fin 4,¬Core (faceEdges p t)) := by
  ext p
  simp only [exteriorFaces,retained_eq_core,coreFaces,Finset.mem_sdiff,Finset.mem_filter,not_exists]
  tauto

end OperatorDerivativeRewrite.Foundation.FourCubeCoreIncident
