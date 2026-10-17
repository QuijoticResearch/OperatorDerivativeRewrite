import Foundation.PeriodicInteriorGaugeKernel
import Mathlib.LinearAlgebra.Quotient.Basic

/-! A closed interior-supported periodic field has nonzero circulation and
survives the quotient by exact periodic vertex gradients. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicInteriorHolonomy
open PeriodicInteriorGaugeKernel
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

def intField (e : Edge) : ℤ := if e.2=0 ∧ interior e then 1 else 0
def field (e : Edge) : ℝ := (intField e : ℝ)

theorem intField_boundary (e : Edge) (he : ¬ interior e) : intField e=0 := by
  simp [intField,he]

theorem intField_closed : ∀ v : Vertex, ∀ i j : Direction, intCurl intField v i j=0 := by decide

theorem field_closed (v : Vertex) (i j : Direction) : curl field v i j=0 := by
  have h := intField_closed v i j
  unfold curl field
  unfold intCurl at h
  exact_mod_cast h

def once : Vertex := shift origin 0
def twice : Vertex := shift once 0
def thrice : Vertex := shift twice 0

theorem cycle_closes : shift thrice 0=origin := by decide

def winding (f : Edge → ℝ) : ℝ := f (origin,0)+f (once,0)+f (twice,0)+f (thrice,0)

theorem gradient_winding_zero (φ : Vertex → ℝ) : winding (gradientMap φ)=0 := by
  change (φ (shift origin 0)-φ origin)+(φ (shift once 0)-φ once)+
    (φ (shift twice 0)-φ twice)+(φ (shift thrice 0)-φ thrice)=0
  rw [cycle_closes]
  change (φ once-φ origin)+(φ twice-φ once)+(φ thrice-φ twice)+(φ origin-φ thrice)=0
  ring

theorem intField_winding :
    intField (origin,0)+intField (once,0)+intField (twice,0)+intField (thrice,0)=2 := by decide

theorem field_winding : winding field=2 := by
  unfold winding field
  exact_mod_cast intField_winding

theorem field_not_gradient : ¬ ∃ φ : Vertex → ℝ, gradientMap φ=field := by
  rintro ⟨φ,hφ⟩
  have he := gradient_winding_zero φ
  rw [hφ,field_winding] at he
  norm_num at he

def witness (e : Interior) : ℝ := field e.val

theorem extend_witness : extend witness=field := by
  funext e
  by_cases he : interior e
  · simp [extend,witness,he]
  · simp [extend,he,field,intField_boundary e he]

theorem incidence_witness_zero : interiorIncidence witness=0 := by
  change incidence (extend witness)=0
  rw [extend_witness]
  ext p
  exact field_closed _ _ _

theorem hessian_witness_zero : hessian.mulVec witness=0 := by
  rw [hessian,← Matrix.mulVec_mulVec,incidenceMatrix_mulVec,incidence_witness_zero,Matrix.mulVec_zero]

def gaugeSpace : Submodule ℝ (Interior → ℝ) := gradientMap.range.comap extend

theorem witness_not_gauge : witness ∉ gaugeSpace := by
  intro h
  change extend witness ∈ gradientMap.range at h
  obtain ⟨φ,hφ⟩ := h
  rw [extend_witness] at hφ
  exact field_not_gradient ⟨φ,hφ⟩

theorem quotient_witness_nonzero :
    (Submodule.Quotient.mk witness : (Interior → ℝ) ⧸ gaugeSpace) ≠ 0 := by
  intro h
  exact witness_not_gauge ((Submodule.Quotient.mk_eq_zero gaugeSpace).mp h)

def hessianMap : (Interior → ℝ) →ₗ[ℝ] (Interior → ℝ) := Matrix.toLin' hessian

theorem gaugeSpace_le_kernel : gaugeSpace ≤ LinearMap.ker hessianMap := by
  intro f hf
  change extend f ∈ gradientMap.range at hf
  obtain ⟨φ,hφ⟩ := hf
  have hi : interiorIncidence f=0 := by
    change incidence (extend f)=0
    rw [← hφ]
    exact incidence_gradient_zero φ
  change hessianMap f=0
  rw [hessianMap,Matrix.toLin'_apply,hessian,← Matrix.mulVec_mulVec,incidenceMatrix_mulVec,hi,
    Matrix.mulVec_zero]

def quotientHessian : ((Interior → ℝ) ⧸ gaugeSpace) →ₗ[ℝ] (Interior → ℝ) :=
  gaugeSpace.liftQ hessianMap gaugeSpace_le_kernel

theorem quotientHessian_witness_zero :
    quotientHessian (Submodule.Quotient.mk witness)=0 := by
  rw [quotientHessian,Submodule.liftQ_apply]
  exact hessian_witness_zero

theorem quotientHessian_not_injective : ¬ Function.Injective quotientHessian := by
  intro h
  have he : quotientHessian (Submodule.Quotient.mk witness)=quotientHessian 0 := by
    rw [quotientHessian_witness_zero,map_zero]
  exact quotient_witness_nonzero (h he)

end OperatorDerivativeRewrite.Foundation.PeriodicInteriorHolonomy
