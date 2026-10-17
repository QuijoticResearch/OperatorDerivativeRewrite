import Foundation.PeriodicMixedLinkEnergy
import Mathlib.LinearAlgebra.Quotient.Basic

/-! A periodic flat field survives the Schur complement of one invertible
local block, including after quotienting exterior restrictions of gradients.
The exterior here is the complement of one block, not all inter-block links. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicOneBlockSchurKernel
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

abbrev Outside := {e : Edge // ¬ localEdge e}

def localRestrict : (Edge → ℝ) →ₗ[ℝ] (Local → ℝ) where
  toFun f e := f e.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def outsideRestrict : (Edge → ℝ) →ₗ[ℝ] (Outside → ℝ) where
  toFun f e := f e.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def outsideExtend : (Outside → ℝ) →ₗ[ℝ] (Edge → ℝ) where
  toFun f e := if he : localEdge e then 0 else f ⟨e,he⟩
  map_add' f g := by ext e; by_cases he : localEdge e <;> simp [he]
  map_smul' r f := by ext e; by_cases he : localEdge e <;> simp [he]

theorem split_reconstruct (f : Edge → ℝ) :
    localExtend (localRestrict f)+outsideExtend (outsideRestrict f)=f := by
  ext e
  change (if he : localEdge e then f e else 0)+(if he : localEdge e then 0 else f e)=f e
  by_cases he : localEdge e <;> simp [he]

def outsideIncidence : (Outside → ℝ) →ₗ[ℝ] (Face → ℝ) := incidence.comp outsideExtend
def outsideMatrix : Matrix Face Outside ℝ := LinearMap.toMatrix' outsideIncidence

theorem outsideMatrix_mulVec (x : Outside → ℝ) :
    outsideMatrix.mulVec x=outsideIncidence x := LinearMap.toMatrix'_mulVec _ _

theorem split_incidence (f : Edge → ℝ) :
    localMatrix.mulVec (localRestrict f)+outsideMatrix.mulVec (outsideRestrict f)=
      incidence f := by
  rw [localMatrix_mulVec,outsideMatrix_mulVec]
  change incidence (localExtend (localRestrict f))+
    incidence (outsideExtend (outsideRestrict f))=incidence f
  rw [← map_add,split_reconstruct]

def coupling : Matrix Local Outside ℝ := localMatrix.transpose*outsideMatrix
def schur : Matrix Outside Outside ℝ :=
  outsideMatrix.transpose*outsideMatrix-
    (outsideMatrix.transpose*localMatrix)*localHessian⁻¹*coupling

theorem local_inverse_cancel (y : Local → ℝ) :
    localHessian⁻¹.mulVec (localHessian.mulVec y)=y := by
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
    (localHessian.isUnit_iff_isUnit_det.mp localHessian_isUnit),Matrix.one_mulVec]

theorem schur_closed_split (x : Outside → ℝ) (y : Local → ℝ)
    (h : localMatrix.mulVec y+outsideMatrix.mulVec x=0) : schur.mulVec x=0 := by
  have hb : outsideMatrix.mulVec x=-(localMatrix.mulVec y) := eq_neg_of_add_eq_zero_right h
  have hc : coupling.mulVec x=-(localHessian.mulVec y) := by
    rw [coupling,← Matrix.mulVec_mulVec,hb,Matrix.mulVec_neg]
    rw [localHessian,← Matrix.mulVec_mulVec]
  have hi : localHessian⁻¹.mulVec (coupling.mulVec x)=-y := by
    rw [hc,Matrix.mulVec_neg,local_inverse_cancel]
  rw [schur,Matrix.sub_mulVec]
  simp only [← Matrix.mulVec_mulVec]
  rw [hb,hi]
  simp only [Matrix.mulVec_neg,sub_self]

def flatField (e : Edge) : ℝ := if e.2=0 then 1 else 0

theorem flatField_closed : incidence flatField=0 := by
  ext p
  change (if p.val.2.1=0 then (1 : ℝ) else 0)+(if p.val.2.2=0 then 1 else 0)-
    (if p.val.2.1=0 then 1 else 0)-(if p.val.2.2=0 then 1 else 0)=0
  ring

def flatOutside : Outside → ℝ := outsideRestrict flatField

theorem flatOutside_schur_zero : schur.mulVec flatOutside=0 := by
  apply schur_closed_split flatOutside (localRestrict flatField)
  rw [flatOutside,split_incidence,flatField_closed]

def start : Vertex := shift (shift origin 1) 1
def once : Vertex := shift start 0
def twice : Vertex := shift once 0
def thrice : Vertex := shift twice 0

theorem cycle_closes : shift thrice 0=start := by decide
theorem cycle_outside : ¬ localEdge (start,0) ∧ ¬ localEdge (once,0) ∧
    ¬ localEdge (twice,0) ∧ ¬ localEdge (thrice,0) := by decide

def winding (f : Outside → ℝ) : ℝ :=
  f ⟨(start,0),cycle_outside.1⟩+f ⟨(once,0),cycle_outside.2.1⟩+
    f ⟨(twice,0),cycle_outside.2.2.1⟩+f ⟨(thrice,0),cycle_outside.2.2.2⟩

def outsideGradient : (Vertex → ℝ) →ₗ[ℝ] (Outside → ℝ) :=
  outsideRestrict.comp gradientMap

theorem gradient_winding_zero (φ : Vertex → ℝ) : winding (outsideGradient φ)=0 := by
  change (φ (shift start 0)-φ start)+(φ (shift once 0)-φ once)+
    (φ (shift twice 0)-φ twice)+(φ (shift thrice 0)-φ thrice)=0
  rw [cycle_closes]
  change (φ once-φ start)+(φ twice-φ once)+(φ thrice-φ twice)+(φ start-φ thrice)=0
  ring

theorem flatOutside_winding : winding flatOutside=4 := by
  change (1 : ℝ)+1+1+1=4
  norm_num

theorem flatOutside_nonzero : flatOutside ≠ 0 := by
  intro h
  have hw := flatOutside_winding
  rw [h] at hw
  norm_num [winding] at hw

theorem schur_not_injective : ¬ Function.Injective schur.mulVec := by
  intro h
  have he : schur.mulVec flatOutside=schur.mulVec 0 := by
    rw [flatOutside_schur_zero,Matrix.mulVec_zero]
  exact flatOutside_nonzero (h he)

theorem schur_not_isUnit : ¬ IsUnit schur := by
  intro h
  exact schur_not_injective (Matrix.mulVec_injective_iff_isUnit.mpr h)

def gaugeSpace : Submodule ℝ (Outside → ℝ) := outsideGradient.range

theorem flatOutside_not_gauge : flatOutside ∉ gaugeSpace := by
  rintro ⟨φ,hφ⟩
  have hw := gradient_winding_zero φ
  rw [hφ,flatOutside_winding] at hw
  norm_num at hw

theorem quotient_flat_nonzero :
    (Submodule.Quotient.mk flatOutside : (Outside → ℝ) ⧸ gaugeSpace) ≠ 0 := by
  intro h
  exact flatOutside_not_gauge ((Submodule.Quotient.mk_eq_zero gaugeSpace).mp h)

def schurMap : (Outside → ℝ) →ₗ[ℝ] (Outside → ℝ) := Matrix.toLin' schur

theorem gaugeSpace_le_kernel : gaugeSpace ≤ LinearMap.ker schurMap := by
  rintro f ⟨φ,rfl⟩
  change schur.mulVec (outsideGradient φ)=0
  apply schur_closed_split _ (localRestrict (gradientMap φ))
  change localMatrix.mulVec (localRestrict (gradientMap φ))+
    outsideMatrix.mulVec (outsideRestrict (gradientMap φ))=0
  rw [split_incidence,incidence_gradient_zero]

def quotientSchur : ((Outside → ℝ) ⧸ gaugeSpace) →ₗ[ℝ] (Outside → ℝ) :=
  gaugeSpace.liftQ schurMap gaugeSpace_le_kernel

theorem quotientSchur_flat_zero : quotientSchur (Submodule.Quotient.mk flatOutside)=0 := by
  rw [quotientSchur,Submodule.liftQ_apply]
  exact flatOutside_schur_zero

theorem quotientSchur_not_injective : ¬ Function.Injective quotientSchur := by
  intro h
  have he : quotientSchur (Submodule.Quotient.mk flatOutside)=quotientSchur 0 := by
    rw [quotientSchur_flat_zero,map_zero]
  exact quotient_flat_nonzero (h he)

end OperatorDerivativeRewrite.Foundation.PeriodicOneBlockSchurKernel
