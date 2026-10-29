import Foundation.FourCubeCoreIncident

/-! Exact source-only value of the744-face exterior remainder.
Finite slot/source certificates precede the universal nonlinear SU(2) identity. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeExteriorSources
open QuaternionSU2Representation OneSidedBlockIncidence OneSidedBlockRank
open FourCubeHaarParity FourCubePinnedCoercivity FourCubeDirichletBox
open FourCubeNativeTransport FourCubeCoreIncident

def sourceEdge (j : Fin 3) : BoxEdge := ![highSource,chordSource,lowSource] j

def SourceMatch (e : BoxEdge) (j : Fin 3) : Prop :=
  e.2=(sourceEdge j).2 ∧ ∀ k : Fin 4,(e.1 k).val=((sourceEdge j).1 k).val

instance sourceMatch_decidable (e : BoxEdge) (j : Fin 3) : Decidable (SourceMatch e j) :=
  inferInstanceAs (Decidable (e.2=(sourceEdge j).2 ∧
    ∀ k : Fin 4,(e.1 k).val=((sourceEdge j).1 k).val))

def plainExterior : Finset BoxFace := faces.filter (fun p => ∀ t : Fin 4,¬Core (faceEdges p t))
def hits (p : BoxFace) : Finset (Fin 4 × Fin 3) :=
  Finset.univ.filter (fun q => SourceMatch (faceEdges p q.1) q.2)
def badFaces : Finset BoxFace := plainExterior.filter (fun p => 1<(hits p).card)
def sourceMultiplicity (j : Fin 3) : ℕ :=
  ∑ p∈plainExterior,∑ t : Fin 4,if SourceMatch (faceEdges p t) j then 1 else 0

theorem bad_faces_zero : badFaces.card=0 := by decide +kernel

theorem source_counts : ∀ j : Fin 3,sourceMultiplicity j=![3,4,3] j := by
  intro j
  fin_cases j <;> decide +kernel

attribute [local irreducible] faces plainExterior hits badFaces sourceMultiplicity

theorem plain_eq_exterior : plainExterior=exteriorFaces := by
  rw [plainExterior]
  exact exterior_filter.symm

theorem source_match_iff (e : BoxEdge) (j : Fin 3) : SourceMatch e j ↔ e=sourceEdge j := by
  constructor
  · rintro ⟨hd,hv⟩
    apply Prod.ext
    · funext k
      exact Fin.ext (hv k)
    · exact hd
  · rintro rfl
    exact ⟨rfl,fun _ => rfl⟩

theorem hits_card_le_one (p : BoxFace) (hp : p∈plainExterior) : (hits p).card ≤ 1 := by
  by_contra h
  have hm : p∈badFaces := by
    rw [badFaces]
    exact Finset.mem_filter.mpr ⟨hp,Nat.lt_of_not_ge h⟩
  have hz : badFaces=∅ := Finset.card_eq_zero.mp bad_faces_zero
  rw [hz] at hm
  exact Finset.notMem_empty p hm

theorem source_label (j : Fin 3) : label (sourceEdge j)=some (.inr j) := by
  fin_cases j
  · exact source_labels.1
  · exact source_labels.2.1
  · exact source_labels.2.2

theorem link_source (b : Fin 3 → SU2) (s : InteriorState) (j : Fin 3) :
    link b s (sourceEdge j)=b j := by rw [link,source_label]

private theorem link_none (b : Fin 3 → SU2) (s : InteriorState) (e : BoxEdge)
    (hn : ¬Core e) (hs : ∀ j : Fin 3,e≠sourceEdge j) : link b s e=1 := by
  have hc : ¬(candidate e∈edges ∧ embed (candidate e)=e) := by
    rintro ⟨hmem,he⟩
    exact hn (he ▸ core_embed ⟨candidate e,hmem⟩)
  have h0 : e≠highSource := hs 0
  have h1 : e≠chordSource := hs 1
  have h2 : e≠lowSource := hs 2
  simp only [link,label,dif_neg hc,if_neg h0,if_neg h1,if_neg h2]

private theorem single_defect (U : SU2) (k : Fin 4) :
    defect ((if (0 : Fin 4)=k then U else 1)*(if (1 : Fin 4)=k then U else 1)*
      (if (2 : Fin 4)=k then U else 1)⁻¹*(if (3 : Fin 4)=k then U else 1)⁻¹)=defect U := by
  fin_cases k <;> simp [defect_inv]

theorem word_source_sum (b : Fin 3 → SU2) (s : InteriorState) (p : BoxFace)
    (hp : p∈plainExterior) : defect (word b s p)=∑ q∈hits p,defect (b q.2) := by
  classical
  have hc (t : Fin 4) : ¬Core (faceEdges p t) := by
    rw [plainExterior] at hp
    exact (Finset.mem_filter.mp hp).2 t
  by_cases hn : (hits p).Nonempty
  · obtain ⟨q,hq⟩ := hn
    have only (r : Fin 4 × Fin 3) (hr : r∈hits p) : r=q :=
      (Finset.card_le_one.mp (hits_card_le_one p hp)) r hr q hq
    have hs : hits p={q} := by
      ext r
      constructor
      · intro hr
        exact Finset.mem_singleton.mpr (only r hr)
      · intro hr
        rw [Finset.mem_singleton] at hr
        simpa only [hr] using hq
    have hq' := hq
    rw [hits] at hq'
    have he : faceEdges p q.1=sourceEdge q.2 :=
      (source_match_iff _ _).mp ((Finset.mem_filter.mp hq').2)
    have hl (t : Fin 4) : link b s (faceEdges p t)=if t=q.1 then b q.2 else 1 := by
      by_cases ht : t=q.1
      · subst t
        rw [if_pos rfl,he,link_source]
      · rw [if_neg ht]
        apply link_none b s _ (hc t)
        intro j hj
        have hh : (t,j)∈hits p := by
          rw [hits]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(source_match_iff _ _).mpr hj⟩
        exact ht (congrArg Prod.fst (only (t,j) hh))
    rw [hs,Finset.sum_singleton]
    unfold word
    simp only [hl]
    exact single_defect _ _
  · have hz : hits p=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hl (t : Fin 4) : link b s (faceEdges p t)=1 := by
      apply link_none b s _ (hc t)
      intro j hj
      apply hn
      refine ⟨(t,j),?_⟩
      rw [hits]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(source_match_iff _ _).mpr hj⟩
    simp only [word,hl,mul_one,inv_one,defect_one,hz,Finset.sum_empty]

private theorem coefficient (b : Fin 3 → SU2) (j : Fin 3) :
    (∑ p∈plainExterior,∑ t : Fin 4,if SourceMatch (faceEdges p t) j then defect (b j) else 0)=
      (sourceMultiplicity j : ℝ)*defect (b j) := by
  rw [sourceMultiplicity]
  simp only [Nat.cast_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> norm_num

theorem hit_sum (b : Fin 3 → SU2) :
    (∑ p∈plainExterior,∑ q∈hits p,defect (b q.2))=
      ∑ j : Fin 3,(sourceMultiplicity j : ℝ)*defect (b j) := by
  calc
    _ = ∑ p∈plainExterior,∑ t : Fin 4,∑ j : Fin 3,
        if SourceMatch (faceEdges p t) j then defect (b j) else 0 := by
      simp only [hits,Finset.sum_filter,Fintype.sum_prod_type]
    _ = ∑ p∈plainExterior,∑ j : Fin 3,∑ t : Fin 4,
        if SourceMatch (faceEdges p t) j then defect (b j) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact Finset.sum_comm
    _ = ∑ j : Fin 3,∑ p∈plainExterior,∑ t : Fin 4,
        if SourceMatch (faceEdges p t) j then defect (b j) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact coefficient b j

/-- Actual nonlinear exterior source cost, uniform in every integrated link assignment. -/
theorem exterior_source_identity (b : Fin 3 → SU2) (s : InteriorState) :
    exteriorAction b s=3*defect (b 0)+4*defect (b 1)+3*defect (b 2) := by
  rw [exteriorAction,← plain_eq_exterior]
  calc
    _ = ∑ p∈plainExterior,∑ q∈hits p,defect (b q.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact word_source_sum b s p hp
    _ = ∑ j : Fin 3,(sourceMultiplicity j : ℝ)*defect (b j) := hit_sum b
    _ = _ := by simp only [source_counts,Fin.sum_univ_three]; norm_num

/-- Complete exact action decomposition for the ACTUAL864-face Dirichlet model. -/
theorem full_action_identity (b : Fin 3 → SU2) (s : InteriorState) :
    action b s=FourCubeBoundaryCubic.fullAction (FourCubeIntegratedCubic.fill (boundary b) s)+
      (∑ e : Interior,(FourCubeNegativeCompletion.multiplicity e : ℝ)*defect (s e))+
      (3*defect (b 0)+4*defect (b 1)+3*defect (b 2)) := by
  rw [action_partition,exterior_source_identity]

theorem axis_defect (i : Fin 3) (t : ℝ) :
    defect (SU2JointPlaquetteCubic.axis i t)=1-Real.cos t := by
  rw [defect,FourCubeWilsonCubic.axis_trace]

/-- Original angle boundary, actual864-face action and all32 unpinned link variables. -/
theorem full_angle_identity (x y z : ℝ) (s : InteriorState) :
    action ![SU2JointPlaquetteCubic.axis 0 x,(SU2JointPlaquetteCubic.axis 1 y)⁻¹,
      (SU2JointPlaquetteCubic.axis 2 z)⁻¹] s=FourCubeIntegratedCubic.cellAction x y z s+
      (∑ e : Interior,(FourCubeNegativeCompletion.multiplicity e : ℝ)*defect (s e))+
      (3*(1-Real.cos x)+4*(1-Real.cos y)+3*(1-Real.cos z)) := by
  rw [full_action_identity,boundary_angles]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    defect_inv,axis_defect]
  rfl

end OperatorDerivativeRewrite.Foundation.FourCubeExteriorSources
