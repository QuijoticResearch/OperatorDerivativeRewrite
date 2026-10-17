import Foundation.OneSidedEffectiveCurvature
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A31-coordinate pin preserving the interior curvature range and its invertible Gram. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedPinnedInterior
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank OneSidedCapComplex
  OneSidedBoundaryGauge OneSidedEffectiveCurvature
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def pole : Interior := ⟨(origin,0),by decide⟩
abbrev Free := {e : Interior // e≠pole}
abbrev FreeField := Free → ℝ

theorem free_card : Fintype.card Free=31 := by decide

def lift : FreeField →ₗ[ℝ] Field where
  toFun y e := if h : e=pole then 0 else y ⟨e,h⟩
  map_add' y z := by funext e; by_cases h : e=pole <;> simp [h]
  map_smul' c y := by funext e; by_cases h : e=pole <;> simp [h]

theorem lift_pole (y : FreeField) : lift y pole=0 := by simp [lift]

theorem lift_free (y : FreeField) (e : Free) : lift y e.val=y e := by simp [lift,e.property]

theorem gauge_pole : gauge pole=1 := by norm_num [OneSidedBlockRank.gauge,pole,originField,originStar]

def pin : Field →ₗ[ℝ] FreeField where
  toFun f e := f e.val-f pole*gauge e.val
  map_add' f g := by
    funext e
    change (f e.val+g e.val)-(f pole+g pole)*gauge e.val=
      (f e.val-f pole*gauge e.val)+(g e.val-g pole*gauge e.val)
    ring
  map_smul' c f := by
    funext e
    change c*f e.val-(c*f pole)*gauge e.val=c*(f e.val-f pole*gauge e.val)
    ring

theorem lift_pin (f : Field) : lift (pin f)=f-f pole • gauge := by
  funext e
  by_cases h : e≠pole
  · simp [lift,pin,h,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  · have he : e=pole := not_ne_iff.mp h
    subst e
    simp [lift,gauge_pole,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]

def pinnedIncidence : FreeField →ₗ[ℝ] Curvature := incidence.comp lift

theorem incidence_lift_pin (f : Field) : incidence (lift (pin f))=incidence f := by
  rw [lift_pin,map_sub,map_smul,gauge_incidence_zero,smul_zero,sub_zero]

theorem pinned_range : LinearMap.range pinnedIncidence=LinearMap.range incidence := by
  apply le_antisymm
  · rintro z ⟨y,hy⟩
    exact ⟨lift y,hy⟩
  · rintro z ⟨f,rfl⟩
    exact ⟨pin f,incidence_lift_pin f⟩

theorem lift_energy_zero_iff (y : FreeField) : realEnergy (extend (lift y))=0 ↔ y=0 := by
  constructor
  · intro h
    have hc : extend (lift y) (origin,0)=0 := by
      change extend (lift y) pole.val=0
      rw [extend_on,lift_pole]
    funext e
    have he := kernel_classification (extend (lift y)) h e.val.val e.val.property
    rw [hc,zero_mul,extend_on,lift_free] at he
    exact he
  · intro h
    apply (incidence_zero_iff (lift y)).mp
    rw [h,map_zero,map_zero]

theorem pinned_injective : Function.Injective pinnedIncidence := by
  intro x y h
  have hz : pinnedIncidence (x-y)=0 := by rw [map_sub,h,sub_self]
  have he : realEnergy (extend (lift (x-y)))=0 := (incidence_zero_iff _).mp hz
  exact sub_eq_zero.mp ((lift_energy_zero_iff _).mp he)

theorem lift_energy_positive (y : FreeField) (hy : y≠0) : 0<realEnergy (extend (lift y)) := by
  by_contra h
  have hz : realEnergy (extend (lift y))=0 :=
    le_antisymm (le_of_not_gt h) (realEnergy_nonneg _)
  exact hy ((lift_energy_zero_iff y).mp hz)

def flatten : Curvature ≃ₗ[ℝ] (FullFace → ℝ) where
  toFun q := Sum.elim q.1 q.2
  invFun f := (fun p => f (.inl p),fun p => f (.inr p))
  left_inv q := by rcases q with ⟨q1,q2⟩; rfl
  right_inv f := by funext p; cases p <;> rfl
  map_add' f g := by funext p; cases p <;> rfl
  map_smul' c f := by funext p; cases p <;> rfl

def localMap : FreeField →ₗ[ℝ] (FullFace → ℝ) := flatten.toLinearMap.comp pinnedIncidence

def boundaryMap : BoundaryField →ₗ[ℝ] (FullFace → ℝ) := flatten.toLinearMap.comp boundaryCurl

def localMatrix : Matrix FullFace Free ℝ := LinearMap.toMatrix' localMap

def boundaryMatrix : Matrix FullFace Boundary ℝ := LinearMap.toMatrix' boundaryMap

def localGram : Matrix Free Free ℝ := localMatrix.transpose*localMatrix

theorem localMatrix_mulVec (y : FreeField) : localMatrix.mulVec y=localMap y :=
  LinearMap.toMatrix'_mulVec _ _

theorem boundaryMatrix_mulVec (eta : BoundaryField) : boundaryMatrix.mulVec eta=boundaryMap eta :=
  LinearMap.toMatrix'_mulVec _ _

theorem localMap_injective : Function.Injective localMap := flatten.injective.comp pinned_injective

theorem localGram_energy (y : FreeField) :
    dotProduct y (localGram.mulVec y)=realEnergy (extend (lift y)) := by
  rw [localGram,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,localMatrix_mulVec]
  change (∑ p : FullFace, (localMap y p)*(localMap y p))=realEnergy (extend (lift y))
  simp only [Fintype.sum_sum_type]
  change (∑ p : Inner, realCurl (extend (lift y)) p*realCurl (extend (lift y)) p)+
    (∑ p : Upper, extend (lift y) p.val.1*extend (lift y) p.val.1)=realEnergy (extend (lift y))
  simp only [← pow_two]
  unfold realEnergy
  congr 1

theorem localGram_positive (y : FreeField) (hy : y≠0) : 0<dotProduct y (localGram.mulVec y) := by
  rw [localGram_energy]
  exact lift_energy_positive y hy

theorem localGram_injective : Function.Injective localGram.mulVec := by
  intro x y h
  have hz : localGram.mulVec (x-y)=0 := by rw [Matrix.mulVec_sub,h,sub_self]
  have he := localGram_energy (x-y)
  rw [hz,dotProduct_zero] at he
  exact sub_eq_zero.mp ((lift_energy_zero_iff _).mp he.symm)

theorem localGram_isUnit : IsUnit localGram := Matrix.mulVec_injective_iff_isUnit.mp localGram_injective

theorem local_inverse_solve (b : FreeField) : localGram.mulVec (localGram⁻¹.mulVec b)=b := by
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    (localGram.isUnit_iff_isUnit_det.mp localGram_isUnit),Matrix.one_mulVec]

end OperatorDerivativeRewrite.Foundation.OneSidedPinnedInterior
