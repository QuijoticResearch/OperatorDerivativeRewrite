import Foundation.PeriodicPhysicalEnergyMinimum

/-! Sparse planar Gram formula and exact integer certificates for the fine energy witness. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicFineEnergyWitnessCertificates
open PeriodicInteriorGaugeKernel PeriodicCoarseGaugeDiagnostics PeriodicFinePhysicalGreen
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def incidenceCoefficient (p : Face) (e : Edge) : ℤ :=
  (if e = (p.val.1,p.val.2.1) then 1 else 0) +
  (if e = (shift p.val.1 p.val.2.1,p.val.2.2) then 1 else 0) -
  (if e = (shift p.val.1 p.val.2.2,p.val.2.1) then 1 else 0) -
  (if e = (p.val.1,p.val.2.2) then 1 else 0)

def intGram (f : Edge → ℤ) (e : Edge) : ℤ :=
  ∑ p : Face, incidenceCoefficient p e * intCurl f p.val.1 p.val.2.1 p.val.2.2

theorem full_matrix_entry (p : Face) (e : Edge) :
    fullIncidenceMatrix p e = (incidenceCoefficient p e : ℝ) := by
  rw [fullIncidenceMatrix, LinearMap.toMatrix'_apply]
  simp [incidence, curl, incidenceCoefficient, Pi.single_apply, eq_comm]

theorem G_entry (f : Edge → ℝ) (e : Edge) :
    G f e = ∑ p : Face, (incidenceCoefficient p e : ℝ) * incidence f p := by
  change fullGram.mulVec f e = _
  rw [fullGram, ← Matrix.mulVec_mulVec, fullIncidence_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, full_matrix_entry]

theorem G_cast (f : Edge → ℤ) :
    G (fun e => (f e : ℝ)) = fun e => (intGram f e : ℝ) := by
  funext e
  rw [G_entry]
  have hc (p : Face) : incidence (fun e => (f e : ℝ)) p =
      (intCurl f p.val.1 p.val.2.1 p.val.2.2 : ℝ) := curl_cast f _ _ _
  simp_rw [hc]
  unfold intGram
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Int.cast_mul]

def aZ (e : Edge) : ℤ := if e.2 = 0 then (-1)^((e.1 1).val/2) else 0

def wZ (e : Edge) : ℤ :=
  if e.2 = 0 ∧ (e.1 0).val % 2 = 1 then 2 * (-1)^((e.1 1).val/2) else 0

def pZ (e : Edge) : ℤ := 3 * wZ e - gradient badPotentialZ e

abbrev Pair := {ij : Direction × Direction // ij.1 < ij.2}

def faceEquiv : Face ≃ Vertex × Pair where
  toFun p := (p.val.1, ⟨p.val.2,p.property⟩)
  invFun p := ⟨(p.1,p.2.val),p.2.property⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by rcases p with ⟨v,⟨ij,hij⟩⟩; rfl

def backShift (v : Vertex) (i : Direction) : Vertex := fun j => v j - if j = i then 1 else 0

def shiftEquiv (i : Direction) : Vertex ≃ Vertex where
  toFun v := shift v i
  invFun v := backShift v i
  left_inv v := by funext j; simp [shift, backShift]
  right_inv v := by funext j; simp [shift, backShift]

theorem sum_vertex_delta (h : Vertex → ℤ) (e : Edge) (i : Direction) :
    (∑ v : Vertex, if e = (v,i) then h v else 0) = if e.2 = i then h e.1 else 0 := by
  rcases e with ⟨v,j⟩
  by_cases hj : j = i <;> simp [Prod.mk.injEq, hj]

theorem sum_shift_delta (h : Vertex → ℤ) (e : Edge) (i j : Direction) :
    (∑ v : Vertex, if e = (shift v j,i) then h v else 0) =
      if e.2 = i then h (backShift e.1 j) else 0 := by
  rw [← (shiftEquiv j).symm.sum_comp (fun v => if e = (shift v j,i) then h v else 0)]
  change (∑ v : Vertex, if e = (shiftEquiv j ((shiftEquiv j).symm v),i) then
    h (backShift v j) else 0) = _
  simp only [Equiv.apply_symm_apply]
  exact sum_vertex_delta (fun v => h (backShift v j)) e i

theorem planar_gram (f : Edge → ℤ)
    (hf : ∀ v : Vertex, ∀ ij : Pair, ij.val ≠ (0,1) →
      intCurl f v ij.val.1 ij.val.2 = 0) (e : Edge) :
    intGram f e =
      (if e.2 = 0 then intCurl f e.1 0 1 - intCurl f (backShift e.1 1) 0 1 else 0) +
      (if e.2 = 1 then intCurl f (backShift e.1 0) 0 1 - intCurl f e.1 0 1 else 0) := by
  unfold intGram
  rw [← faceEquiv.symm.sum_comp
    (fun p => incidenceCoefficient p e * intCurl f p.val.1 p.val.2.1 p.val.2.2)]
  rw [Fintype.sum_prod_type]
  have hs (v : Vertex) : (∑ ij : Pair,
      incidenceCoefficient (faceEquiv.symm (v,ij)) e * intCurl f v ij.val.1 ij.val.2) =
      incidenceCoefficient (⟨(v,(0,1)),by change (0 : Direction) < 1; decide⟩ : Face) e * intCurl f v 0 1 := by
    apply Finset.sum_eq_single (⟨(0,1),by decide⟩ : Pair)
    · intro ij _ hij
      have hne : ij.val ≠ (0,1) := fun h => hij (Subtype.ext h)
      rw [hf v ij hne, mul_zero]
    · simp
  change (∑ v : Vertex, ∑ ij : Pair,
    incidenceCoefficient (faceEquiv.symm (v,ij)) e * intCurl f v ij.val.1 ij.val.2) = _
  simp_rw [hs]
  simp only [incidenceCoefficient, add_mul, sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_vertex_delta, sum_shift_delta, sum_shift_delta, sum_vertex_delta]
  by_cases h0 : e.2 = 0 <;> by_cases h1 : e.2 = 1 <;> simp [h0,h1]

set_option maxHeartbeats 16000000 in
-- Kernel arithmetic checks the actual finite plaquette and edge cases after sparse reduction.
theorem a_support : ∀ (v : Vertex) (ij : Pair), ij.val ≠ (0,1) →
    intCurl aZ v ij.val.1 ij.val.2 = 0 := by decide

set_option maxHeartbeats 16000000 in
-- Kernel arithmetic checks the actual finite plaquette and edge cases after sparse reduction.
theorem p_support : ∀ (v : Vertex) (ij : Pair), ij.val ≠ (0,1) →
    intCurl pZ v ij.val.1 ij.val.2 = 0 := by decide

set_option maxHeartbeats 16000000 in
-- Kernel arithmetic checks the actual finite plaquette and edge cases after sparse reduction.
theorem gram_a_int : ∀ e : Edge, intGram aZ e = 2 * aZ e := by
  intro e
  rw [planar_gram aZ a_support]
  revert e
  decide

set_option maxHeartbeats 16000000 in
-- Kernel arithmetic checks the actual finite plaquette and edge cases after sparse reduction.
theorem gram_p_int : ∀ e : Edge, intGram pZ e = 6 * pZ e - 12 * aZ e := by
  intro e
  rw [planar_gram pZ p_support]
  revert e
  decide

end OperatorDerivativeRewrite.Foundation.PeriodicFineEnergyWitnessCertificates
