import Foundation.OneSidedBoundaryCycleData
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Actual boundary cycles span the gauge-orthogonal physical boundary space. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedBoundaryCycles
open OneSidedBlockRank OneSidedCapComplex OneSidedBoundaryGauge OneSidedBoundaryCycleData
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def edgeEquiv : Fin 80 ≃ Boundary := Equiv.ofBijective point point_bijective

def cycleMatrix : Matrix Boundary (Fin 34) ℝ :=
  fun b j => (cycleData (edgeEquiv.symm b) j : ℝ)

theorem cycle_at_point (k : Fin 80) (j : Fin 34) :
    cycleMatrix (point k) j=(cycleData k j : ℝ) := by
  change (cycleData (edgeEquiv.symm (edgeEquiv k)) j : ℝ)=_
  rw [Equiv.symm_apply_apply]

theorem sum_boundary (f : Boundary → ℝ) : (∑ k : Fin 80, f (point k))=∑ b : Boundary, f b :=
  edgeEquiv.sum_comp f

theorem gradient_formula (k : Fin 80) (phi : Potential) :
    boundaryGradient phi (point k)=
      ∑ v : Fin 48, (gradientData k v : ℝ)*phi (vertexPoint v) := by
  change phi (target (.inr (point k)))-phi (source (.inr (point k)))=_
  rw [point_target,point_source]
  simp [gradientData,sub_mul,Finset.sum_sub_distrib]

theorem real_cycle_balance (j : Fin 34) (v : Fin 48) :
    (∑ k : Fin 80, (cycleData k j : ℝ)*(gradientData k v : ℝ))=0 := by
  exact_mod_cast cycle_balance j v

theorem cycle_orthogonal (j : Fin 34) (phi : Potential) :
    dotProduct (fun b => cycleMatrix b j) (boundaryGradient phi)=0 := by
  change (∑ b : Boundary, cycleMatrix b j*boundaryGradient phi b)=0
  rw [← sum_boundary (fun b => cycleMatrix b j*boundaryGradient phi b)]
  simp_rw [cycle_at_point,gradient_formula]
  calc
    _ = ∑ v : Fin 48, (∑ k : Fin 80, (cycleData k j : ℝ)*(gradientData k v : ℝ))*
        phi (vertexPoint v) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc,← Finset.sum_mul]
    _ = 0 := by simp only [real_cycle_balance,zero_mul,Finset.sum_const_zero]

theorem cycle_chord_action (y : Fin 34 → ℝ) (i : Fin 34) :
    cycleMatrix.mulVec y (point (chord i))=y i := by
  simp [Matrix.mulVec,dotProduct,cycle_at_point,chord_identity]

def cycleMap : (Fin 34 → ℝ) →ₗ[ℝ] BoundaryField := Matrix.toLin' cycleMatrix

theorem cycle_injective : Function.Injective cycleMap := by
  intro x y h
  funext i
  have ht := congrFun h (point (chord i))
  change cycleMatrix.mulVec x (point (chord i))=cycleMatrix.mulVec y (point (chord i)) at ht
  simpa only [cycle_chord_action] using ht

theorem cycle_rank : Module.finrank ℝ (LinearMap.range cycleMap)=34 := by
  rw [LinearMap.finrank_range_of_inj cycle_injective]
  simp

def gradientMatrix : Matrix Boundary FullVertex ℝ := LinearMap.toMatrix' boundaryGradient

def divergence : BoundaryField →ₗ[ℝ] Potential := Matrix.toLin' gradientMatrix.transpose

theorem divergence_pairing (eta : BoundaryField) (phi : Potential) :
    dotProduct phi (divergence eta)=dotProduct eta (boundaryGradient phi) := by
  rw [divergence,Matrix.toLin'_apply,Matrix.dotProduct_transpose_mulVec,
    gradientMatrix,LinearMap.toMatrix'_mulVec]

theorem divergence_zero_iff (eta : BoundaryField) :
    divergence eta=0 ↔ ∀ phi : Potential, dotProduct eta (boundaryGradient phi)=0 := by
  constructor
  · intro h phi
    rw [← divergence_pairing,h,dotProduct_zero]
  · intro h
    apply dotProduct_self_eq_zero.mp
    rw [divergence_pairing,h]

theorem divergence_rank : Module.finrank ℝ (LinearMap.range divergence)=46 := by
  calc
    _ = gradientMatrix.transpose.rank := by
      simpa only [divergence,Matrix.toLin_eq_toLin'] using
        (Matrix.rank_eq_finrank_range_toLin gradientMatrix.transpose
          (Pi.basisFun ℝ FullVertex) (Pi.basisFun ℝ Boundary)).symm
    _ = gradientMatrix.rank := Matrix.rank_transpose _
    _ = 46 := by
      rw [Matrix.rank_eq_finrank_range_toLin gradientMatrix
        (Pi.basisFun ℝ Boundary) (Pi.basisFun ℝ FullVertex),Matrix.toLin_eq_toLin',
        gradientMatrix,Matrix.toLin'_toMatrix',boundary_gradient_rank]

theorem physical_finrank : Module.finrank ℝ (LinearMap.ker divergence)=34 := by
  have ht := LinearMap.finrank_range_add_finrank_ker divergence
  rw [divergence_rank,boundaryField_finrank] at ht
  omega

theorem cycles_physical : LinearMap.range cycleMap≤LinearMap.ker divergence := by
  rintro eta ⟨y,rfl⟩
  apply (divergence_zero_iff _).mpr
  intro phi
  have ht : cycleMatrix.transpose.mulVec (boundaryGradient phi)=0 := by
    funext j
    exact cycle_orthogonal j phi
  change dotProduct (cycleMatrix.mulVec y) (boundaryGradient phi)=0
  rw [dotProduct_comm,← Matrix.dotProduct_transpose_mulVec,ht,dotProduct_zero]

theorem cycle_range : LinearMap.range cycleMap=LinearMap.ker divergence := by
  apply Submodule.eq_of_le_of_finrank_eq cycles_physical
  rw [cycle_rank,physical_finrank]

theorem physical_representation (eta : BoundaryField)
    (ho : ∀ phi : Potential, dotProduct eta (boundaryGradient phi)=0) :
    ∃ y : Fin 34 → ℝ, cycleMatrix.mulVec y=eta := by
  have h : eta∈LinearMap.ker divergence := (divergence_zero_iff eta).mpr ho
  rw [← cycle_range] at h
  exact h

end OperatorDerivativeRewrite.Foundation.OneSidedBoundaryCycles
