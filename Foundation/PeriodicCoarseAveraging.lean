import Foundation.PeriodicInteriorGaugeKernel

/-! Actual dyadic boundary averaging: fine side4, coarse side2, and normalized adjoint lift. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseAveraging
open PeriodicInteriorGaugeKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

abbrev CoarseVertex := Direction → ZMod 2
abbrev CoarseEdge := CoarseVertex × Direction
abbrev Bits := Direction → ZMod 2

def coarseBlock (v : Vertex) : CoarseVertex := fun i => ((v i).val/2 : ℕ)
def fineBits (v : Vertex) : Bits := fun i => ((v i).val%2 : ℕ)
def fineVertex (q : CoarseVertex) (b : Bits) : Vertex :=
  fun i => (2*(q i).val+(b i).val : ℕ)
def oddEdge (e : Edge) : Prop := fineBits e.1 e.2 = 1
instance oddEdge_decidable (e : Edge) : Decidable (oddEdge e) :=
  inferInstanceAs (Decidable (fineBits e.1 e.2=1))

theorem boundary_iff_odd : ∀ e : Edge, ¬ interior e ↔ oddEdge e := by decide

theorem coarseBlock_fineVertex : ∀ q : CoarseVertex, ∀ b : Bits,
    coarseBlock (fineVertex q b)=q := by decide

theorem fineBits_fineVertex : ∀ q : CoarseVertex, ∀ b : Bits,
    fineBits (fineVertex q b)=b := by decide

theorem fineVertex_reconstruct : ∀ v : Vertex,
    fineVertex (coarseBlock v) (fineBits v)=v := by decide

theorem face_bit_count : ∀ i : Direction,
    ((Finset.univ : Finset Bits).filter (fun b => b i=1)).card=8 := by decide

def edgeEquiv : Edge ≃ CoarseEdge × Bits where
  toFun e := ((coarseBlock e.1,e.2),fineBits e.1)
  invFun p := (fineVertex p.1.1 p.2,p.1.2)
  left_inv e := by
    change (fineVertex (coarseBlock e.1) (fineBits e.1),e.2)=e
    rw [fineVertex_reconstruct]
  right_inv p := by
    rcases p with ⟨⟨q,i⟩,b⟩
    simp [coarseBlock_fineVertex, fineBits_fineVertex]

def average : (Edge → ℝ) →ₗ[ℝ] (CoarseEdge → ℝ) :=
  LinearMap.pi (fun q => (1/8 : ℝ) • ∑ b : Bits,
    if b q.2=1 then LinearMap.proj (fineVertex q.1 b,q.2) else 0)

def flatLift : (CoarseEdge → ℝ) →ₗ[ℝ] (Edge → ℝ) :=
  LinearMap.pi (fun e => if oddEdge e then LinearMap.proj (coarseBlock e.1,e.2) else 0)

def normalizedLift : (CoarseEdge → ℝ) →ₗ[ℝ] (Edge → ℝ) := (1/8 : ℝ) • flatLift

theorem average_apply (f : Edge → ℝ) (q : CoarseEdge) :
    average f q = (1/8 : ℝ)*∑ b : Bits,
      if b q.2=1 then f (fineVertex q.1 b,q.2) else 0 := by
  simp [average, LinearMap.sum_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : b q.2=1 <;> simp [h]

theorem flatLift_apply (c : CoarseEdge → ℝ) (e : Edge) :
    flatLift c e = if oddEdge e then c (coarseBlock e.1,e.2) else 0 := by
  by_cases h : oddEdge e <;> simp [flatLift, h]

theorem normalizedLift_apply (c : CoarseEdge → ℝ) (e : Edge) :
    normalizedLift c e = (1/8 : ℝ)*(if oddEdge e then c (coarseBlock e.1,e.2) else 0) := by
  simp [normalizedLift, flatLift_apply, smul_eq_mul]

theorem average_flatLift (c : CoarseEdge → ℝ) : average (flatLift c)=c := by
  funext q
  rw [average_apply]
  have hh (b : Bits) : (if b q.2=1 then flatLift c (fineVertex q.1 b,q.2) else 0) =
      if b q.2=1 then c q else 0 := by
    by_cases h : b q.2=1 <;>
      simp [h, flatLift_apply, oddEdge, fineBits_fineVertex, coarseBlock_fineVertex]
  simp_rw [hh]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  rw [face_bit_count]
  ring

theorem average_normalizedLift (c : CoarseEdge → ℝ) :
    average (normalizedLift c) = (1/8 : ℝ) • c := by
  rw [normalizedLift, LinearMap.smul_apply, map_smul, average_flatLift]

theorem lift_is_adjoint (f : Edge → ℝ) (c : CoarseEdge → ℝ) :
    dotProduct f (normalizedLift c) = dotProduct (average f) c := by
  unfold dotProduct
  rw [← edgeEquiv.symm.sum_comp (fun e => f e*normalizedLift c e), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  rw [average_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  change f (fineVertex q.1 b,q.2)*normalizedLift c (fineVertex q.1 b,q.2) = _
  rw [normalizedLift_apply]
  simp only [oddEdge, fineBits_fineVertex, coarseBlock_fineVertex]
  by_cases h : b q.2=1 <;> simp [h] <;> ring

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseAveraging
