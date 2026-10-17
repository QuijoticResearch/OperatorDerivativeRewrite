import Foundation.PeriodicCoarseAveraging

/-! Coarse curl support and interior orthogonality without an assumed interior inverse. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseCurl
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

abbrev CoarseFace := {p : CoarseVertex × (Direction × Direction) // p.2.1 < p.2.2}

def coarseShift (q : CoarseVertex) (i : Direction) : CoarseVertex :=
  fun k => q k+if k=i then 1 else 0

def coarseCurl (c : CoarseEdge → ℝ) (q : CoarseVertex) (i j : Direction) : ℝ :=
  c (q,i)+c (coarseShift q i,j)-c (coarseShift q j,i)-c (q,j)

def coarseIncidence : (CoarseEdge → ℝ) →ₗ[ℝ] (CoarseFace → ℝ) where
  toFun c p := coarseCurl c p.val.1 p.val.2.1 p.val.2.2
  map_add' c d := by ext p; simp [coarseCurl]; ring
  map_smul' r c := by ext p; simp [coarseCurl, smul_eq_mul]; ring

def coarseGradient : (CoarseVertex → ℝ) →ₗ[ℝ] (CoarseEdge → ℝ) where
  toFun φ e := φ (coarseShift e.1 e.2)-φ e.1
  map_add' φ ψ := by ext e; simp; ring
  map_smul' r φ := by ext e; simp [smul_eq_mul]; ring

theorem coarseShift_commute (q : CoarseVertex) (i j : Direction) :
    coarseShift (coarseShift q i) j=coarseShift (coarseShift q j) i := by
  funext k
  simp only [coarseShift]
  abel

theorem coarseCurl_gradient (φ : CoarseVertex → ℝ) (q : CoarseVertex) (i j : Direction) :
    coarseCurl (coarseGradient φ) q i j=0 := by
  change φ (coarseShift q i)-φ q +
    (φ (coarseShift (coarseShift q i) j)-φ (coarseShift q i)) -
    (φ (coarseShift (coarseShift q j) i)-φ (coarseShift q j)) -
    (φ (coarseShift q j)-φ q)=0
  rw [coarseShift_commute q i j]
  ring

theorem coarseBlock_shift : ∀ v : Vertex, ∀ i : Direction,
    coarseBlock (shift v i) =
      if oddEdge (v,i) then coarseShift (coarseBlock v) i else coarseBlock v := by decide

theorem oddEdge_shift_other : ∀ v : Vertex, ∀ i j : Direction, i ≠ j →
    (oddEdge (shift v i,j) ↔ oddEdge (v,j)) := by decide

theorem flatLift_curl (c : CoarseEdge → ℝ) (v : Vertex) (i j : Direction) (hij : i ≠ j) :
    curl (flatLift c) v i j =
      if oddEdge (v,i) ∧ oddEdge (v,j) then coarseCurl c (coarseBlock v) i j else 0 := by
  unfold curl
  simp only [flatLift_apply, oddEdge_shift_other v i j hij,
    oddEdge_shift_other v j i hij.symm, coarseBlock_shift]
  by_cases hi : oddEdge (v,i) <;> by_cases hj : oddEdge (v,j) <;>
    simp [hi, hj, coarseCurl]

theorem curl_smul (r : ℝ) (f : Edge → ℝ) (v : Vertex) (i j : Direction) :
    curl (r • f) v i j=r*curl f v i j := by
  simp only [curl, Pi.smul_apply, smul_eq_mul]
  ring

theorem normalizedLift_curl (c : CoarseEdge → ℝ) (v : Vertex) (i j : Direction) (hij : i ≠ j) :
    curl (normalizedLift c) v i j = (1/8 : ℝ)*
      (if oddEdge (v,i) ∧ oddEdge (v,j) then coarseCurl c (coarseBlock v) i j else 0) := by
  rw [normalizedLift, LinearMap.smul_apply, curl_smul, flatLift_curl c v i j hij]

theorem flatLift_gradient (φ : CoarseVertex → ℝ) :
    flatLift (coarseGradient φ)=gradientMap (fun v => φ (coarseBlock v)) := by
  funext e
  rw [flatLift_apply]
  change (if oddEdge e then φ (coarseShift (coarseBlock e.1) e.2)-φ (coarseBlock e.1) else 0) =
    φ (coarseBlock (shift e.1 e.2))-φ (coarseBlock e.1)
  rw [coarseBlock_shift]
  by_cases h : oddEdge e <;> simp [h]

theorem interior_corner_zero (y : Interior → ℝ) (v : Vertex) (i j : Direction) (hij : i ≠ j)
    (hi : oddEdge (v,i)) (hj : oddEdge (v,j)) : curl (extend y) v i j=0 := by
  have hni := (boundary_iff_odd (v,i)).mpr hi
  have hnj := (boundary_iff_odd (v,j)).mpr hj
  have hnsi := (boundary_iff_odd (shift v j,i)).mpr
    ((oddEdge_shift_other v j i hij.symm).mpr hi)
  have hnsj := (boundary_iff_odd (shift v i,j)).mpr
    ((oddEdge_shift_other v i j hij).mpr hj)
  simp [curl, extend, hni, hnj, hnsi, hnsj]

theorem incidence_pointwise_orthogonal (y : Interior → ℝ) (c : CoarseEdge → ℝ) (p : Face) :
    interiorIncidence y p * incidence (normalizedLift c) p=0 := by
  have hij : p.val.2.1 ≠ p.val.2.2 := ne_of_lt p.property
  change curl (extend y) p.val.1 p.val.2.1 p.val.2.2 *
    curl (normalizedLift c) p.val.1 p.val.2.1 p.val.2.2=0
  by_cases h : oddEdge (p.val.1,p.val.2.1) ∧ oddEdge (p.val.1,p.val.2.2)
  · rw [interior_corner_zero y _ _ _ hij h.1 h.2, zero_mul]
  · rw [normalizedLift_curl c _ _ _ hij]
    simp [h]

theorem incidence_orthogonal (y : Interior → ℝ) (c : CoarseEdge → ℝ) :
    dotProduct (interiorIncidence y) (incidence (normalizedLift c))=0 := by
  apply Finset.sum_eq_zero
  intro p _
  exact incidence_pointwise_orthogonal y c p

def fineEnergy (f : Edge → ℝ) : ℝ := ∑ p : Face, (incidence f p)^2

theorem fineEnergy_nonneg (f : Edge → ℝ) : 0 ≤ fineEnergy f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem interior_energy_split (y : Interior → ℝ) (c : CoarseEdge → ℝ) :
    fineEnergy (extend y+normalizedLift c)=fineEnergy (extend y)+fineEnergy (normalizedLift c) := by
  simp only [fineEnergy, map_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have h : incidence (extend y) p * incidence (normalizedLift c) p=0 :=
    incidence_pointwise_orthogonal y c p
  nlinarith [h]

theorem interior_minimum_lower (y : Interior → ℝ) (c : CoarseEdge → ℝ) :
    fineEnergy (normalizedLift c) ≤ fineEnergy (extend y+normalizedLift c) := by
  rw [interior_energy_split]
  exact le_add_of_nonneg_left (fineEnergy_nonneg _)

theorem interior_minimum_attained (c : CoarseEdge → ℝ) :
    fineEnergy (extend 0+normalizedLift c)=fineEnergy (normalizedLift c) := by
  rw [map_zero, zero_add]

theorem interior_minimum_not_unique (c : CoarseEdge → ℝ) : ∃ y : Interior → ℝ,
    y ≠ 0 ∧ fineEnergy (extend y+normalizedLift c)=fineEnergy (normalizedLift c) := by
  refine ⟨witness, witness_nonzero, ?_⟩
  have he : fineEnergy (extend witness)=0 := witness_energy_zero
  rw [interior_energy_split, he, zero_add]

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseCurl
