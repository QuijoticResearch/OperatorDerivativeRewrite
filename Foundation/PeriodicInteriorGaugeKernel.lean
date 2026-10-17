import Foundation.OneSidedBlockIncidence
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! An actual periodic plaquette incidence matrix has a nonzero interior-supported
gauge kernel when every side-two block's interior links are eliminated together.
This concerns the unrestricted global operator, not a gauge quotient or one block. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicInteriorGaugeKernel
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

abbrev Direction := Fin 4
abbrev Vertex := Direction → ZMod 4
abbrev Edge := Vertex × Direction
abbrev Face := {p : Vertex × (Direction × Direction) // p.2.1 < p.2.2}

def shift (v : Vertex) (i : Direction) : Vertex := fun k => v k+if k=i then 1 else 0

theorem shift_commute (v : Vertex) (i j : Direction) :
    shift (shift v i) j=shift (shift v j) i := by
  funext k
  simp only [shift]
  abel

def block (v : Vertex) : Direction → ℕ := fun i => (v i).val/2
def interior (e : Edge) : Prop := block e.1=block (shift e.1 e.2)
instance interior_decidable (e : Edge) : Decidable (interior e) := inferInstanceAs (Decidable (_=_))
abbrev Interior := {e : Edge // interior e}

def origin : Vertex := fun _ => 0
def potential (v : Vertex) : ℤ := if v 0=1 ∨ v 0=2 then 1 else 0
def gradient (φ : Vertex → ℤ) (e : Edge) : ℤ := φ (shift e.1 e.2)-φ e.1
def intCurl (f : Edge → ℤ) (v : Vertex) (i j : Direction) : ℤ :=
  f (v,i)+f (shift v i,j)-f (shift v j,i)-f (v,j)

theorem gradient_curl_zero (φ : Vertex → ℤ) (v : Vertex) (i j : Direction) :
    intCurl (gradient φ) v i j=0 := by
  unfold intCurl gradient
  rw [shift_commute v i j]
  ring

def gauge : Edge → ℤ := gradient potential

theorem gauge_boundary_zero : ∀ e : Edge, ¬ interior e → gauge e=0 := by decide
theorem origin_edge_interior : interior (origin,0) := by decide
theorem gauge_origin_value : gauge (origin,0)=1 := by decide

def realGauge (e : Edge) : ℝ := (gauge e : ℝ)
def curl (f : Edge → ℝ) (v : Vertex) (i j : Direction) : ℝ :=
  f (v,i)+f (shift v i,j)-f (shift v j,i)-f (v,j)

theorem realGauge_curl (v : Vertex) (i j : Direction) : curl realGauge v i j=0 := by
  have h := gradient_curl_zero potential v i j
  unfold curl realGauge
  change gauge (v,i)+gauge (shift v i,j)-gauge (shift v j,i)-gauge (v,j)=0 at h
  exact_mod_cast h

def incidence : (Edge → ℝ) →ₗ[ℝ] (Face → ℝ) where
  toFun f p := curl f p.val.1 p.val.2.1 p.val.2.2
  map_add' f g := by ext p; simp [curl]; ring
  map_smul' r f := by ext p; simp [curl,smul_eq_mul]; ring

def gradientMap : (Vertex → ℝ) →ₗ[ℝ] (Edge → ℝ) where
  toFun φ e := φ (shift e.1 e.2)-φ e.1
  map_add' φ ψ := by ext e; simp; ring
  map_smul' r φ := by ext e; simp [smul_eq_mul]; ring

theorem incidence_gradient_zero (φ : Vertex → ℝ) : incidence (gradientMap φ)=0 := by
  ext p
  change φ (shift p.val.1 p.val.2.1)-φ p.val.1+
    (φ (shift (shift p.val.1 p.val.2.1) p.val.2.2)-φ (shift p.val.1 p.val.2.1))-
    (φ (shift (shift p.val.1 p.val.2.2) p.val.2.1)-φ (shift p.val.1 p.val.2.2))-
    (φ (shift p.val.1 p.val.2.2)-φ p.val.1)=0
  rw [shift_commute]
  ring

theorem incidence_comp_gradient : incidence.comp gradientMap=0 := by
  apply LinearMap.ext
  intro φ
  exact incidence_gradient_zero φ

theorem realGauge_is_gradient : realGauge=gradientMap (fun v => (potential v : ℝ)) := by
  funext e
  simp [realGauge,gauge,gradient,gradientMap]

def extend : (Interior → ℝ) →ₗ[ℝ] (Edge → ℝ) where
  toFun f e := if he : interior e then f ⟨e,he⟩ else 0
  map_add' f g := by ext e; by_cases he : interior e <;> simp [he]
  map_smul' r f := by ext e; by_cases he : interior e <;> simp [he]

def interiorIncidence : (Interior → ℝ) →ₗ[ℝ] (Face → ℝ) := incidence.comp extend
def witness (e : Interior) : ℝ := realGauge e.val

theorem extend_witness : extend witness=realGauge := by
  funext e
  by_cases he : interior e
  · simp [extend,witness,he]
  · simp [extend,he,realGauge,gauge_boundary_zero e he]

theorem witness_nonzero : witness ≠ 0 := by
  intro h
  have he := congrFun h (⟨(origin,0),origin_edge_interior⟩ : Interior)
  change (gauge (origin,0) : ℝ)=0 at he
  rw [gauge_origin_value] at he
  norm_num at he

theorem incidence_witness_zero : interiorIncidence witness=0 := by
  change incidence (extend witness)=0
  rw [extend_witness]
  ext p
  exact realGauge_curl _ _ _

def incidenceMatrix : Matrix Face Interior ℝ := LinearMap.toMatrix' interiorIncidence
def hessian : Matrix Interior Interior ℝ := incidenceMatrix.transpose*incidenceMatrix

theorem incidenceMatrix_mulVec (f : Interior → ℝ) :
    incidenceMatrix.mulVec f=interiorIncidence f := LinearMap.toMatrix'_mulVec _ _

theorem incidenceMatrix_witness_zero : incidenceMatrix.mulVec witness=0 := by
  rw [incidenceMatrix_mulVec,incidence_witness_zero]

theorem hessian_witness_zero : hessian.mulVec witness=0 := by
  rw [hessian,← Matrix.mulVec_mulVec,incidenceMatrix_witness_zero,Matrix.mulVec_zero]

theorem hessian_not_injective : ¬ Function.Injective hessian.mulVec := by
  intro h
  have he : hessian.mulVec witness=hessian.mulVec 0 := by
    rw [hessian_witness_zero,Matrix.mulVec_zero]
  exact witness_nonzero (h he)

theorem hessian_no_left_inverse : ¬ ∃ B : Matrix Interior Interior ℝ, B*hessian=1 := by
  rintro ⟨B,hB⟩
  have he := congrArg (fun M : Matrix Interior Interior ℝ => M.mulVec witness) hB
  rw [← Matrix.mulVec_mulVec,hessian_witness_zero,Matrix.mulVec_zero,Matrix.one_mulVec] at he
  exact witness_nonzero he.symm

def squaredSize (f : Interior → ℝ) : ℝ := ∑ e, (f e)^2
def quadraticEnergy (f : Interior → ℝ) : ℝ := ∑ p, (interiorIncidence f p)^2

theorem witness_squaredSize_pos : 0 < squaredSize witness := by
  unfold squaredSize
  apply Finset.sum_pos' (fun e _ => sq_nonneg (witness e))
  refine ⟨(⟨(origin,0),origin_edge_interior⟩ : Interior),Finset.mem_univ _,?_⟩
  change 0 < (gauge (origin,0) : ℝ)^2
  rw [gauge_origin_value]
  norm_num

theorem witness_energy_zero : quadraticEnergy witness=0 := by
  simp [quadraticEnergy,incidence_witness_zero]

theorem no_positive_matrix_coercivity (c : ℝ) (hc : 0 < c) :
    ¬ (∀ f : Interior → ℝ, c*squaredSize f ≤ ∑ e, f e*(hessian.mulVec f) e) := by
  intro h
  have he := h witness
  rw [hessian_witness_zero] at he
  simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero] at he
  have hp := mul_pos hc witness_squaredSize_pos
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicInteriorGaugeKernel
