import Foundation.OneSidedPinnedInterior
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Actual Gaussian elimination for the one-sided block after a proved gauge pin. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedSchurForm
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank OneSidedCapComplex
  OneSidedBoundaryGauge OneSidedEffectiveCurvature OneSidedPinnedInterior
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def coupling : Matrix Free Boundary ℝ := localMatrix.transpose*boundaryMatrix

def boundaryGram : Matrix Boundary Boundary ℝ := boundaryMatrix.transpose*boundaryMatrix

def schur : Matrix Boundary Boundary ℝ := boundaryGram-coupling.transpose*localGram⁻¹*coupling

def response (eta : BoundaryField) : FreeField := -(localGram⁻¹.mulVec (coupling.mulVec eta))

def residual (eta : BoundaryField) : FullFace → ℝ :=
  localMatrix.mulVec (response eta)+boundaryMatrix.mulVec eta

def reducedEnergy (eta : BoundaryField) : ℝ := dotProduct (residual eta) (residual eta)

def jointEnergy (y : FreeField) (eta : BoundaryField) : ℝ :=
  dotProduct (localMatrix.mulVec y+boundaryMatrix.mulVec eta)
    (localMatrix.mulVec y+boundaryMatrix.mulVec eta)

theorem residual_normal (eta : BoundaryField) : localMatrix.transpose.mulVec (residual eta)=0 := by
  rw [residual,Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
  change localGram.mulVec (response eta)+coupling.mulVec eta=0
  rw [response,Matrix.mulVec_neg,local_inverse_solve]
  abel

theorem residual_orthogonal (eta : BoundaryField) (y : FreeField) :
    dotProduct (localMatrix.mulVec y) (residual eta)=0 := by
  rw [dotProduct_comm,← Matrix.dotProduct_transpose_mulVec,residual_normal,dotProduct_zero]

theorem schur_action (eta : BoundaryField) :
    schur.mulVec eta=boundaryMatrix.transpose.mulVec (residual eta) := by
  simp only [schur,boundaryGram,coupling,Matrix.sub_mulVec,← Matrix.mulVec_mulVec,
    Matrix.transpose_mul,Matrix.transpose_transpose,residual,response,
    Matrix.mulVec_add,Matrix.mulVec_neg]
  abel

theorem schur_energy (eta : BoundaryField) :
    dotProduct eta (schur.mulVec eta)=reducedEnergy eta := by
  rw [schur_action,Matrix.dotProduct_transpose_mulVec]
  have ho : dotProduct (residual eta) (localMatrix.mulVec (response eta))=0 := by
    rw [dotProduct_comm,residual_orthogonal]
  unfold reducedEnergy
  conv_rhs => rhs; rw [residual]
  rw [dotProduct_add,ho,zero_add]

theorem completed_square (y : FreeField) (eta : BoundaryField) :
    jointEnergy y eta=reducedEnergy eta+realEnergy (extend (lift (y-response eta))) := by
  have hd : localMatrix.mulVec y+boundaryMatrix.mulVec eta=
      residual eta+localMatrix.mulVec (y-response eta) := by
    rw [residual,Matrix.mulVec_sub]
    abel
  have ho := residual_orthogonal eta (y-response eta)
  have ho' : dotProduct (residual eta) (localMatrix.mulVec (y-response eta))=0 := by
    rw [dotProduct_comm,ho]
  have he : dotProduct (localMatrix.mulVec (y-response eta))
      (localMatrix.mulVec (y-response eta))=realEnergy (extend (lift (y-response eta))) := by
    rw [← Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec]
    exact localGram_energy _
  unfold jointEnergy
  rw [hd,dotProduct_add,add_dotProduct,add_dotProduct,ho,ho',he]
  simp only [zero_add,add_zero,reducedEnergy]

theorem unique_minimizer (y : FreeField) (eta : BoundaryField) :
    jointEnergy y eta=reducedEnergy eta ↔ y=response eta := by
  rw [completed_square,add_eq_left,lift_energy_zero_iff,sub_eq_zero]

theorem reducedEnergy_nonnegative (eta : BoundaryField) : 0≤reducedEnergy eta := by
  unfold reducedEnergy dotProduct
  exact Finset.sum_nonneg (fun p _ => mul_self_nonneg _)

theorem reducedEnergy_zero_iff (eta : BoundaryField) : reducedEnergy eta=0 ↔ residual eta=0 := by
  constructor
  · intro h
    have hs : (∑ p : FullFace, (residual eta p)^2)=0 := by
      simpa [reducedEnergy,dotProduct,pow_two] using h
    have hp := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => sq_nonneg (residual eta p))).mp hs
    funext p
    exact (pow_eq_zero_iff (by decide : 2≠0)).mp (hp p (Finset.mem_univ _))
  · intro h
    simp [reducedEnergy,h]

theorem schur_hermitian : schur.IsHermitian := by
  have hC : localGram.IsHermitian := by
    simpa [localGram] using Matrix.isHermitian_conjTranspose_mul_self localMatrix
  have hB : boundaryGram.IsHermitian := by
    simpa [boundaryGram] using Matrix.isHermitian_conjTranspose_mul_self boundaryMatrix
  have hK : (coupling.transpose*localGram⁻¹*coupling).IsHermitian := by
    simpa using Matrix.isHermitian_conjTranspose_mul_mul coupling hC.inv
  exact hB.sub hK

theorem schur_posSemidef : schur.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg schur_hermitian
  intro eta
  change 0≤dotProduct eta (schur.mulVec eta)
  rw [schur_energy]
  exact reducedEnergy_nonnegative eta

theorem schur_zero_iff_residual (eta : BoundaryField) : schur.mulVec eta=0 ↔ residual eta=0 := by
  constructor
  · intro h
    apply (reducedEnergy_zero_iff eta).mp
    rw [← schur_energy,h,dotProduct_zero]
  · intro h
    rw [schur_action,h,Matrix.mulVec_zero]

theorem residual_curvature (eta : BoundaryField) : residual eta=
    flatten (pinnedIncidence (response eta)+boundaryCurl eta) := by
  simp only [residual,localMatrix_mulVec,boundaryMatrix_mulVec,localMap,boundaryMap,
    LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,map_add]

theorem residual_zero_iff_effective (eta : BoundaryField) :
    residual eta=0 ↔ effectiveCurvature eta=0 := by
  constructor
  · intro h
    have hc : pinnedIncidence (response eta)+boundaryCurl eta=0 := by
      apply flatten.injective
      rw [map_zero]
      exact (residual_curvature eta).symm.trans h
    change incidence (lift (response eta))+boundaryCurl eta=0 at hc
    change (LinearMap.range incidence).mkQ (boundaryCurl eta)=0
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    refine ⟨-lift (response eta),?_⟩
    rw [map_neg]
    calc
      -incidence (lift (response eta))=
          -incidence (lift (response eta))+(incidence (lift (response eta))+boundaryCurl eta) := by
        rw [hc,add_zero]
      _ = boundaryCurl eta := by abel
  · intro h
    change (LinearMap.range incidence).mkQ (boundaryCurl eta)=0 at h
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero] at h
    have hp : boundaryCurl eta∈LinearMap.range pinnedIncidence := by rw [pinned_range]; exact h
    obtain ⟨y,hy⟩ := hp
    have he : localMatrix.mulVec y=boundaryMatrix.mulVec eta := by
      rw [localMatrix_mulVec,boundaryMatrix_mulVec]
      change flatten (pinnedIncidence y)=flatten (boundaryCurl eta)
      exact congrArg flatten hy
    have hr : residual eta=localMatrix.mulVec (response eta+y) := by
      rw [residual,Matrix.mulVec_add,he]
    have ho := residual_orthogonal eta (response eta+y)
    rw [← hr] at ho
    exact (reducedEnergy_zero_iff eta).mp ho

def schurMap : BoundaryField →ₗ[ℝ] BoundaryField := Matrix.toLin' schur

theorem kernel_schur : LinearMap.ker schurMap=LinearMap.range boundaryGradient := by
  rw [← kernel_effective]
  ext eta
  change schur.mulVec eta=0 ↔ effectiveCurvature eta=0
  rw [schur_zero_iff_residual,residual_zero_iff_effective]

theorem schur_kernel_finrank : Module.finrank ℝ (LinearMap.ker schurMap)=46 := by
  rw [kernel_schur,boundary_gradient_rank]

theorem schur_rank : Module.finrank ℝ (LinearMap.range schurMap)=34 := by
  have h := LinearMap.finrank_range_add_finrank_ker schurMap
  rw [schur_kernel_finrank,boundaryField_finrank] at h
  omega

theorem schur_energy_zero_iff_gauge (eta : BoundaryField) :
    dotProduct eta (schur.mulVec eta)=0 ↔ eta∈LinearMap.range boundaryGradient := by
  rw [schur_energy,reducedEnergy_zero_iff,residual_zero_iff_effective]
  change eta∈LinearMap.ker effectiveCurvature ↔ eta∈LinearMap.range boundaryGradient
  rw [kernel_effective]

theorem physical_positive (eta : BoundaryField) (hn : eta≠0)
    (ho : ∀ phi : Potential, dotProduct eta (boundaryGradient phi)=0) :
    0<dotProduct eta (schur.mulVec eta) := by
  by_contra h
  have he : dotProduct eta (schur.mulVec eta)=0 :=
    le_antisymm (le_of_not_gt h) (by rw [schur_energy]; exact reducedEnergy_nonnegative eta)
  obtain ⟨phi,hphi⟩ := (schur_energy_zero_iff_gauge eta).mp he
  have hz := ho phi
  rw [hphi] at hz
  have hs : (∑ b : Boundary, (eta b)^2)=0 := by simpa only [dotProduct,pow_two] using hz
  have hp := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg (eta b))).mp hs
  apply hn
  funext b
  exact (pow_eq_zero_iff (by decide : 2≠0)).mp (hp b (Finset.mem_univ _))

end OperatorDerivativeRewrite.Foundation.OneSidedSchurForm
