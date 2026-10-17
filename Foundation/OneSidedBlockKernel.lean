import Foundation.OneSidedBlockIncidence

/-! Exact classification of the one-sided block's interior energy kernel.
The field is classified on retained edges; off-domain values are unrestricted. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedBlockKernel
open OneSidedBlockIncidence
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

theorem inner_zero (f : EdgeData → ℝ) (h : realEnergy f=0) (p : FaceData)
    (hp : p∈innerFaces) : realCurl f p=0 := by
  have hi := Finset.single_le_sum (fun q (_ : q∈innerFaces) => sq_nonneg (realCurl f q)) hp
  have hu : 0≤∑ q∈upperFaces, (f q.1)^2 :=
    Finset.sum_nonneg (fun q _ => sq_nonneg _)
  have hb : (realCurl f p)^2≤realEnergy f := le_trans hi (le_add_of_nonneg_right hu)
  rw [h] at hb
  exact (sq_eq_zero_iff).mp (le_antisymm hb (sq_nonneg _))

theorem upper_zero (f : EdgeData → ℝ) (h : realEnergy f=0)
    (p : EdgeData × Fin 4) (hp : p∈upperFaces) : f p.1=0 := by
  have hi : 0≤∑ q∈innerFaces, (realCurl f q)^2 :=
    Finset.sum_nonneg (fun q _ => sq_nonneg _)
  have hu := Finset.single_le_sum (fun q (_ : q∈upperFaces) => sq_nonneg (f q.1)) hp
  have hb : (f p.1)^2≤realEnergy f := le_trans hu (le_add_of_nonneg_left hi)
  rw [h] at hb
  exact (sq_eq_zero_iff).mp (le_antisymm hb (sq_nonneg _))

theorem upper_witness : ∀ e∈edges, e.1≠origin → ∃ j : Fin 4, (e,j)∈upperFaces := by decide

theorem origin_face_geometry : ∀ j : Fin 3, (origin,(0,j.succ))∈innerFaces := by decide

theorem shifted_edge_geometry : ∀ i j : Fin 4, i≠j →
    (shifted origin i,j)∈edges ∧ shifted origin i≠origin := by decide

theorem off_origin_zero (f : EdgeData → ℝ) (h : realEnergy f=0) (e : EdgeData)
    (he : e∈edges) (hv : e.1≠origin) : f e=0 := by
  obtain ⟨j,hj⟩ := upper_witness e he hv
  exact upper_zero f h (e,j) hj

theorem origin_values_equal (f : EdgeData → ℝ) (h : realEnergy f=0) (i : Fin 4) :
    f (origin,i)=f (origin,0) := by
  have hs (j : Fin 3) : f (origin,j.succ)=f (origin,0) := by
    have h01 : (0 : Fin 4)≠j.succ := Ne.symm (Fin.succ_ne_zero j)
    have h1 := shifted_edge_geometry 0 j.succ h01
    have h2 := shifted_edge_geometry j.succ 0 (Fin.succ_ne_zero j)
    have hz1 := off_origin_zero f h (shifted origin 0,j.succ) h1.1 h1.2
    have hz2 := off_origin_zero f h (shifted origin j.succ,0) h2.1 h2.2
    have hc := inner_zero f h (origin,(0,j.succ)) (origin_face_geometry j)
    change f (origin,0)+f (shifted origin 0,j.succ)-
      f (shifted origin j.succ,0)-f (origin,j.succ)=0 at hc
    rw [hz1,hz2] at hc
    linarith
  exact Fin.cases rfl hs i

theorem kernel_classification (f : EdgeData → ℝ) (h : realEnergy f=0) :
    ∀ e∈edges, f e=f (origin,0)*originField e := by
  intro e he
  by_cases hv : e.1=origin
  · rcases e with ⟨v,i⟩
    dsimp at hv
    subst v
    rw [origin_values_equal f h i]
    simp [originField,originStar]
  · rw [off_origin_zero f h e he hv]
    simp [originField,originStar,hv]

theorem inner_edge_geometry : ∀ p∈innerFaces,
    (p.1,p.2.1)∈edges ∧ (shifted p.1 p.2.1,p.2.2)∈edges ∧
      (shifted p.1 p.2.2,p.2.1)∈edges ∧ (p.1,p.2.2)∈edges := by decide

theorem realEnergy_congr (f g : EdgeData → ℝ) (h : ∀ e∈edges, f e=g e) :
    realEnergy f=realEnergy g := by
  unfold realEnergy
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨h1,h2,h3,h4⟩ := inner_edge_geometry p hp
    simp only [realCurl,h _ h1,h _ h2,h _ h3,h _ h4]
  · apply Finset.sum_congr rfl
    intro p hp
    have he : p.1∈edges := (Finset.mem_filter.mp hp).2.1
    rw [h _ he]

theorem scalar_origin_zero (c : ℝ) : realEnergy (fun e => c*originField e)=0 := by
  unfold realEnergy
  have hi : ∑ p∈innerFaces, (realCurl (fun e => c*originField e) p)^2=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hs : realCurl (fun e => c*originField e) p=c*realCurl originField p := by
      simp only [realCurl]
      ring
    rw [hs,originField_curl,originStar_inner_zero p hp]
    norm_num
  have hu : ∑ p∈upperFaces, (c*originField p.1)^2=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp only [originField,originStar_upper_zero p hp,Int.cast_zero,mul_zero,zero_pow (by decide : 2≠0)]
  rw [hi,hu,add_zero]

theorem energy_zero_iff (f : EdgeData → ℝ) : realEnergy f=0 ↔
    ∀ e∈edges, f e=f (origin,0)*originField e := by
  constructor
  · exact kernel_classification f
  · intro h
    rw [realEnergy_congr f (fun e => f (origin,0)*originField e) h]
    exact scalar_origin_zero _

def OrthogonalToGauge (f : EdgeData → ℝ) : Prop := ∑ e∈edges, f e*originField e=0

theorem physical_kernel_zero (f : EdgeData → ℝ) (h : realEnergy f=0)
    (hg : OrthogonalToGauge f) : ∀ e∈edges, f e=0 := by
  have hs : (∑ e∈edges, f e*originField e)=f (origin,0)*4 := by
    calc
      _ = ∑ e∈edges, f (origin,0)*(originField e)^2 := by
        apply Finset.sum_congr rfl
        intro e he
        rw [kernel_classification f h e he]
        ring
      _ = f (origin,0)*4 := by rw [← Finset.mul_sum,originField_norm_sq]
  have hc : f (origin,0)=0 := by
    change (∑ e∈edges, f e*originField e)=0 at hg
    rw [hs] at hg
    linarith
  intro e he
  rw [kernel_classification f h e he,hc,zero_mul]

theorem physical_energy_positive (f : EdgeData → ℝ) (hg : OrthogonalToGauge f)
    (hf : ∃ e∈edges, f e≠0) : 0<realEnergy f := by
  by_contra h
  have hz : realEnergy f=0 := le_antisymm (le_of_not_gt h) (realEnergy_nonneg f)
  obtain ⟨e,he,hn⟩ := hf
  exact hn (physical_kernel_zero f hz hg e he)

end OperatorDerivativeRewrite.Foundation.OneSidedBlockKernel
