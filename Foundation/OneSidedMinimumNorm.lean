import Foundation.OneSidedCanonicalInverse

/-! The canonical least-norm interior response and the complete gauge orbit of minimizers. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedMinimumNorm
open OneSidedBlockRank OneSidedCapComplex OneSidedBoundaryGauge OneSidedPinnedInterior
  OneSidedPhysicalProjection OneSidedSchurForm OneSidedCanonicalInverse
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def canonicalResponse (eta : BoundaryField) : Field := -(M.mulVec (fullCoupling.mulVec eta))

def fullEnergy (f : Field) (eta : BoundaryField) : ℝ :=
  dotProduct (fullMatrix.mulVec f+boundaryMatrix.mulVec eta)
    (fullMatrix.mulVec f+boundaryMatrix.mulVec eta)

theorem fullMatrix_W : fullMatrix*W=localMatrix := by
  rw [W,← Matrix.mul_assoc,fullMatrix_P,fullMatrix_lift]

theorem response_eq_frame (eta : BoundaryField) :
    canonicalResponse eta=W.mulVec (response eta) := by
  have h : M*fullCoupling=W*localGram⁻¹*coupling := by
    rw [M,Matrix.mul_assoc,W_coupling]
  simp only [canonicalResponse,response,Matrix.mulVec_neg,Matrix.mulVec_mulVec]
  rw [h,Matrix.mul_assoc]

theorem response_orthogonal (eta : BoundaryField) :
    dotProduct (canonicalResponse eta) gauge=0 := by
  have h : P.mulVec (canonicalResponse eta)=canonicalResponse eta := by
    rw [canonicalResponse,Matrix.mulVec_neg,Matrix.mulVec_mulVec,P_M]
  rw [← h]
  exact P_pairing _

theorem response_curvature (eta : BoundaryField) :
    fullMatrix.mulVec (canonicalResponse eta)=localMatrix.mulVec (response eta) := by
  rw [response_eq_frame,Matrix.mulVec_mulVec,fullMatrix_W]

theorem fullMatrix_pin (f : Field) : fullMatrix.mulVec f=localMatrix.mulVec (pin f) := by
  rw [← fullMatrix_lift,← Matrix.mulVec_mulVec,liftMatrix_mulVec,lift_pin,
    Matrix.mulVec_sub,Matrix.mulVec_smul,fullMatrix_gauge,smul_zero,sub_zero]

theorem full_residual_orthogonal (eta : BoundaryField) (f : Field) :
    dotProduct (fullMatrix.mulVec f) (residual eta)=0 := by
  rw [fullMatrix_pin]
  exact residual_orthogonal eta _

theorem full_completed_square (f : Field) (eta : BoundaryField) :
    fullEnergy f eta=reducedEnergy eta+
      dotProduct (fullMatrix.mulVec (f-canonicalResponse eta))
        (fullMatrix.mulVec (f-canonicalResponse eta)) := by
  have hd : fullMatrix.mulVec f+boundaryMatrix.mulVec eta=
      residual eta+fullMatrix.mulVec (f-canonicalResponse eta) := by
    rw [OneSidedSchurForm.residual,Matrix.mulVec_sub,response_curvature]
    abel
  have ho := full_residual_orthogonal eta (f-canonicalResponse eta)
  have ho' : dotProduct (residual eta) (fullMatrix.mulVec (f-canonicalResponse eta))=0 := by
    rw [dotProduct_comm,ho]
  unfold fullEnergy
  rw [hd,dotProduct_add,add_dotProduct,add_dotProduct,ho,ho']
  simp only [zero_add,add_zero,reducedEnergy]

theorem fullEnergy_lower_bound (f : Field) (eta : BoundaryField) :
    reducedEnergy eta≤fullEnergy f eta := by
  rw [full_completed_square]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _))

theorem response_minimizes (eta : BoundaryField) :
    fullEnergy (canonicalResponse eta) eta=reducedEnergy eta := by
  rw [full_completed_square,sub_self,Matrix.mulVec_zero,dotProduct_zero,add_zero]

theorem fullMatrix_kernel (f : Field) :
    fullMatrix.mulVec f=0 ↔ ∃ c : ℝ, f=c • gauge := by
  constructor
  · intro h
    have hc : fullGram.mulVec f=0 := by
      rw [fullGram,← Matrix.mulVec_mulVec,h,Matrix.mulVec_zero]
    have hp : P.mulVec f=0 := by
      rw [← M_fullGram,← Matrix.mulVec_mulVec,hc,Matrix.mulVec_zero]
    rw [P_action] at hp
    exact ⟨dotProduct f gauge/4,sub_eq_zero.mp hp⟩
  · rintro ⟨c,rfl⟩
    rw [Matrix.mulVec_smul,fullMatrix_gauge,smul_zero]

theorem minimizers_gauge_orbit (f : Field) (eta : BoundaryField) :
    fullEnergy f eta=reducedEnergy eta ↔
      ∃ c : ℝ, f=canonicalResponse eta+c • gauge := by
  rw [full_completed_square,add_eq_left,dotProduct_self_eq_zero,fullMatrix_kernel]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hc)
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    rw [hc]
    abel

theorem gauge_orbit_norm (eta : BoundaryField) (c : ℝ) :
    dotProduct (canonicalResponse eta+c • gauge) (canonicalResponse eta+c • gauge)=
      dotProduct (canonicalResponse eta) (canonicalResponse eta)+4*c^2 := by
  have ho : dotProduct gauge (canonicalResponse eta)=0 := by
    rw [dotProduct_comm,response_orthogonal]
  simp only [add_dotProduct,dotProduct_add,dotProduct_smul,smul_dotProduct,
    smul_eq_mul,response_orthogonal,ho,gauge_norm]
  ring

theorem minimizer_norm_lower_bound (f : Field) (eta : BoundaryField)
    (h : fullEnergy f eta=reducedEnergy eta) :
    dotProduct (canonicalResponse eta) (canonicalResponse eta)≤dotProduct f f := by
  obtain ⟨c,rfl⟩ := (minimizers_gauge_orbit f eta).mp h
  rw [gauge_orbit_norm]
  exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (sq_nonneg c))

theorem minimum_norm_unique (f : Field) (eta : BoundaryField)
    (h : fullEnergy f eta=reducedEnergy eta)
    (hn : dotProduct f f≤dotProduct (canonicalResponse eta) (canonicalResponse eta)) :
    f=canonicalResponse eta := by
  obtain ⟨c,rfl⟩ := (minimizers_gauge_orbit f eta).mp h
  rw [gauge_orbit_norm] at hn
  have hc : c=0 := by nlinarith [sq_nonneg c]
  rw [hc,zero_smul,add_zero]

theorem orthogonal_minimizer_unique (f : Field) (eta : BoundaryField)
    (h : fullEnergy f eta=reducedEnergy eta) (ho : dotProduct f gauge=0) :
    f=canonicalResponse eta := by
  obtain ⟨c,rfl⟩ := (minimizers_gauge_orbit f eta).mp h
  rw [add_dotProduct,response_orthogonal,smul_dotProduct,gauge_norm,smul_eq_mul] at ho
  have hc : c=0 := by linarith
  rw [hc,zero_smul,add_zero]

end OperatorDerivativeRewrite.Foundation.OneSidedMinimumNorm
