import Foundation.SU2ExponentialMembership

/-! A direct finite model of the companion's one-sided four-dimensional block. -/
namespace OperatorDerivativeRewrite.Foundation.OneSidedBlockIncidence
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

abbrev Vertex := Fin 4 → Fin 2
abbrev EdgeData := Vertex × Fin 4
abbrev FaceData := Vertex × (Fin 4 × Fin 4)

def edges : Finset EdgeData := Finset.univ.filter (fun e => e.1 e.2=0)
def innerFaces : Finset FaceData := Finset.univ.filter
  (fun p => p.2.1 < p.2.2 ∧ p.1 p.2.1=0 ∧ p.1 p.2.2=0)
def upperFaces : Finset (EdgeData × Fin 4) := Finset.univ.filter
  (fun p => p.1∈edges ∧ p.2≠p.1.2 ∧ p.1.1 p.2=1)

theorem edges_card : edges.card=32 := by decide
theorem innerFaces_card : innerFaces.card=24 := by decide
theorem upperFaces_card : upperFaces.card=48 := by decide
theorem allFaces_card : innerFaces.card+upperFaces.card=72 := by
  rw [innerFaces_card, upperFaces_card]

def shifted (v : Vertex) (a : Fin 4) : Vertex := Function.update v a 1
def origin : Vertex := fun _ => 0
def originStar (e : EdgeData) : ℤ := if e.1=origin then 1 else 0
def curl (f : EdgeData → ℤ) (p : FaceData) : ℤ :=
  f (p.1,p.2.1)+f (shifted p.1 p.2.1,p.2.2)-
    f (shifted p.1 p.2.2,p.2.1)-f (p.1,p.2.2)

theorem originStar_inner_zero : ∀ p∈innerFaces, curl originStar p=0 := by decide
theorem originStar_upper_zero : ∀ p∈upperFaces, originStar p.1=0 := by decide

def energy (f : EdgeData → ℤ) : ℤ :=
  (∑ p∈innerFaces, (curl f p)^2) + (∑ p∈upperFaces, (f p.1)^2)

theorem originStar_energy_zero : energy originStar=0 := by
  unfold energy
  have hi : ∑ p∈innerFaces, (curl originStar p)^2=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [originStar_inner_zero p hp]
    norm_num
  have hu : ∑ p∈upperFaces, (originStar p.1)^2=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [originStar_upper_zero p hp]
    norm_num
  rw [hi, hu, add_zero]

theorem originStar_norm_sq : (∑ e∈edges, (originStar e)^2)=4 := by decide
theorem originStar_nonzero : originStar (origin,0)=1 := by decide

theorem incidence_square_count : 4*innerFaces.card+upperFaces.card=144 := by
  rw [innerFaces_card, upperFaces_card]

def realCurl (f : EdgeData → ℝ) (p : FaceData) : ℝ :=
  f (p.1,p.2.1)+f (shifted p.1 p.2.1,p.2.2)-
    f (shifted p.1 p.2.2,p.2.1)-f (p.1,p.2.2)
def realEnergy (f : EdgeData → ℝ) : ℝ :=
  (∑ p∈innerFaces, (realCurl f p)^2) + (∑ p∈upperFaces, (f p.1)^2)
def originField (e : EdgeData) : ℝ := (originStar e:ℝ)

theorem realEnergy_nonneg (f : EdgeData → ℝ) : 0 ≤ realEnergy f := by
  apply add_nonneg <;> apply Finset.sum_nonneg <;> intro p hp <;> exact sq_nonneg _

theorem originField_curl (p : FaceData) : realCurl originField p=(curl originStar p:ℝ) := by
  simp [realCurl, originField, curl]

theorem originField_energy_zero : realEnergy originField=0 := by
  unfold realEnergy
  have hi : ∑ p∈innerFaces, (realCurl originField p)^2=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [originField_curl, originStar_inner_zero p hp]
    norm_num
  have hu : ∑ p∈upperFaces, (originField p.1)^2=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp only [originField, originStar_upper_zero p hp, Int.cast_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [hi, hu, add_zero]

theorem originField_norm_sq : (∑ e∈edges, (originField e)^2)=4 := by
  unfold originField
  exact_mod_cast originStar_norm_sq

end OperatorDerivativeRewrite.Foundation.OneSidedBlockIncidence
