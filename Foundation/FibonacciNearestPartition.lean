import Foundation.FibonacciSphereWitness
import Mathlib.Data.Finset.Max

/-! Least-index nearest Fibonacci-center assignment and exact separation of four supported rays. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FibonacciNearestPartition
open FibonacciSphereWitness

abbrev Direction := Fin 3 → ℝ

def dot (v : Direction) (j : Fin 16) : ℝ := ∑ q, v q*center 16 j q

def maximizers (v : Direction) : Finset (Fin 16) := by
  classical
  exact Finset.univ.filter (fun j => ∀ i, dot v i ≤ dot v j)

theorem maximizers_nonempty (v : Direction) : (maximizers v).Nonempty := by
  classical
  obtain ⟨j,hj,hmax⟩ := Finset.univ.exists_max_image (dot v) Finset.univ_nonempty
  exact ⟨j,by simp only [maximizers,Finset.mem_filter,Finset.mem_univ,true_and]; exact fun i => hmax i (Finset.mem_univ i)⟩

def label (v : Direction) : Fin 16 := (maximizers v).min' (maximizers_nonempty v)

theorem label_max (v : Direction) (j : Fin 16) : dot v j ≤ dot v (label v) := by
  have h := Finset.min'_mem (maximizers v) (maximizers_nonempty v)
  change label v ∈ Finset.univ.filter (fun k => ∀ i, dot v i ≤ dot v k) at h
  exact (Finset.mem_filter.mp h).2 j

theorem dot_scale (a : ℝ) (v : Direction) (j : Fin 16) :
    dot (fun q => a*v q) j=a*dot v j := by
  simp only [dot,Finset.mul_sum,mul_assoc]

theorem label_scale (a : ℝ) (ha : 0 < a) (v : Direction) :
    label (fun q => a*v q)=label v := by
  classical
  have he : maximizers (fun q => a*v q)=maximizers v := by
    ext j
    simp only [maximizers,Finset.mem_filter,Finset.mem_univ,true_and,dot_scale,mul_le_mul_iff_right₀ ha]
  unfold label
  apply le_antisymm
  · apply Finset.min'_le
    rw [he]
    exact Finset.min'_mem _ _
  · apply Finset.min'_le
    rw [← he]
    exact Finset.min'_mem _ _

def distanceSq (v : Direction) (j : Fin 16) : ℝ := ∑ q, (v q-center 16 j q)^2

theorem distance_identity (v : Direction) (j : Fin 16) :
    distanceSq v j=(∑ q, (v q)^2)+1-2*dot v j := by
  have hu := center_unit 16 j
  simp only [distanceSq,dot,Fin.sum_univ_three] at *
  nlinarith

theorem nearest (v : Direction) (j : Fin 16) : distanceSq v (label v) ≤ distanceSq v j := by
  rw [distance_identity,distance_identity]
  linarith [label_max v j]

def score (r : Fin 4) (c : Direction) : ℝ := ![c 1,-c 1,c 2,-c 2] r

def ray (r : Fin 4) : Direction := ![![0,1,0],![0,-1,0],![0,0,1],![0,0,-1]] r

theorem dot_ray (r : Fin 4) (j : Fin 16) : dot (ray r) j=score r (center 16 j) := by
  fin_cases r <;> simp [dot,ray,score,Fin.sum_univ_three]

theorem ray_witness (r : Fin 4) : ∃ j : Fin 16, (3:ℝ)/4 ≤ dot (ray r) j := by
  fin_cases r
  · exact ⟨⟨7,by decide⟩,by simpa [dot_ray,score] using witness_seven⟩
  · exact ⟨⟨6,by decide⟩,by simpa [dot_ray,score] using witness_six⟩
  · exact ⟨⟨0,by decide⟩,by simpa [dot_ray,score] using witness_north⟩
  · exact ⟨⟨15,by decide⟩,by simpa [dot_ray,score] using witness_south⟩

theorem selected_score (r : Fin 4) : (3:ℝ)/4 ≤ score r (center 16 (label (ray r))) := by
  obtain ⟨j,hj⟩ := ray_witness r
  rw [← dot_ray]
  exact hj.trans (label_max _ j)

theorem four_scores_injective {ι : Type*} (c : ι → Direction)
    (hunit : ∀ j, ∑ q, (c j q)^2=1) (f : Fin 4 → ι)
    (hscore : ∀ r, (3:ℝ)/4 ≤ score r (c (f r))) : Function.Injective f := by
  intro r s he
  have hr := hscore r
  have hs := hscore s
  rw [← he] at hs
  have hu := hunit (f r)
  have h0 := sq_nonneg (c (f r) 0)
  have h1p := sq_nonneg (c (f r) 1-3/4)
  have h1m := sq_nonneg (c (f r) 1+3/4)
  have h2p := sq_nonneg (c (f r) 2-3/4)
  have h2m := sq_nonneg (c (f r) 2+3/4)
  simp only [Fin.sum_univ_three] at hu
  fin_cases r <;> fin_cases s
  all_goals first | rfl | skip
  all_goals norm_num [score] at hr hs h0 h1p h1m h2p h2m hu ⊢
  all_goals nlinarith

def rayLabels : Fin 4 ↪ Fin 16 :=
  ⟨fun r => label (ray r),four_scores_injective (center 16) (center_unit 16) _ selected_score⟩

end OperatorDerivativeRewrite.Foundation.FibonacciNearestPartition
