import Foundation.PeriodicOneBlockSchurKernel

/-! Actual Gaussian elimination on the one-block periodic split: exact
completed square, unique local minimizer, and positive semidefinite Schur form. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicSchurCompletedSquare
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity
  PeriodicOneBlockSchurKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def response (x : Outside → ℝ) : Local → ℝ :=
  -(localHessian⁻¹.mulVec (coupling.mulVec x))

def residual (x : Outside → ℝ) : Face → ℝ :=
  localMatrix.mulVec (response x)+outsideMatrix.mulVec x

def jointEnergy (y : Local → ℝ) (x : Outside → ℝ) : ℝ :=
  dotProduct (localMatrix.mulVec y+outsideMatrix.mulVec x)
    (localMatrix.mulVec y+outsideMatrix.mulVec x)

def reducedEnergy (x : Outside → ℝ) : ℝ := dotProduct (residual x) (residual x)

theorem local_inverse_solve (b : Local → ℝ) :
    localHessian.mulVec (localHessian⁻¹.mulVec b)=b := by
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    (localHessian.isUnit_iff_isUnit_det.mp localHessian_isUnit),Matrix.one_mulVec]

theorem residual_normal (x : Outside → ℝ) : localMatrix.transpose.mulVec (residual x)=0 := by
  rw [residual,Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
  change localHessian.mulVec (response x)+coupling.mulVec x=0
  rw [response,Matrix.mulVec_neg,local_inverse_solve]
  abel

theorem residual_orthogonal (x : Outside → ℝ) (y : Local → ℝ) :
    dotProduct (localMatrix.mulVec y) (residual x)=0 := by
  rw [dotProduct_comm,← Matrix.dotProduct_transpose_mulVec,residual_normal,dotProduct_zero]

theorem schur_action (x : Outside → ℝ) :
    schur.mulVec x=outsideMatrix.transpose.mulVec (residual x) := by
  simp only [schur,Matrix.sub_mulVec,← Matrix.mulVec_mulVec,residual,response,
    Matrix.mulVec_add,Matrix.mulVec_neg]
  abel

theorem schur_energy (x : Outside → ℝ) :
    dotProduct x (schur.mulVec x)=reducedEnergy x := by
  rw [schur_action,Matrix.dotProduct_transpose_mulVec]
  have ho : dotProduct (residual x) (localMatrix.mulVec (response x))=0 := by
    rw [dotProduct_comm,residual_orthogonal]
  unfold reducedEnergy
  conv_rhs => rhs; rw [residual]
  rw [dotProduct_add,ho,zero_add]

theorem completed_square (y : Local → ℝ) (x : Outside → ℝ) :
    jointEnergy y x=reducedEnergy x+energy (y-response x) := by
  have hd : localMatrix.mulVec y+outsideMatrix.mulVec x=
      residual x+localMatrix.mulVec (y-response x) := by
    rw [residual,Matrix.mulVec_sub]
    abel
  have ho := residual_orthogonal x (y-response x)
  have ho' : dotProduct (residual x) (localMatrix.mulVec (y-response x))=0 := by
    rw [dotProduct_comm,ho]
  have he : dotProduct (localMatrix.mulVec (y-response x))
      (localMatrix.mulVec (y-response x))=energy (y-response x) := by
    rw [← Matrix.dotProduct_transpose_mulVec]
    rw [Matrix.mulVec_mulVec]
    change dotProduct (y-response x) (localHessian.mulVec (y-response x))=_
    exact hessian_energy _
  unfold jointEnergy
  rw [hd,dotProduct_add,add_dotProduct,add_dotProduct,ho,ho',he]
  simp only [zero_add,add_zero,reducedEnergy]

theorem completed_square_coercive (y : Local → ℝ) (x : Outside → ℝ) :
    reducedEnergy x+3*squaredSize (y-response x) ≤ jointEnergy y x := by
  rw [completed_square]
  have hc := energy_coercive (y-response x)
  linarith

theorem local_energy_zero_iff (y : Local → ℝ) : energy y=0 ↔ y=0 := by
  constructor
  · intro h
    have hc := energy_coercive y
    have hn : 0 ≤ squaredSize y := Finset.sum_nonneg (fun e _ => sq_nonneg _)
    apply (squaredSize_zero_iff y).mp
    linarith
  · intro h
    simp [h,energy]

theorem unique_minimizer (y : Local → ℝ) (x : Outside → ℝ) :
    jointEnergy y x=reducedEnergy x ↔ y=response x := by
  rw [completed_square,add_eq_left,local_energy_zero_iff,sub_eq_zero]

theorem reducedEnergy_nonneg (x : Outside → ℝ) : 0 ≤ reducedEnergy x := by
  unfold reducedEnergy dotProduct
  exact Finset.sum_nonneg (fun p _ => mul_self_nonneg _)

theorem schur_hermitian : schur.IsHermitian := by
  have hC : localHessian.IsHermitian := by
    simpa [localHessian] using Matrix.isHermitian_conjTranspose_mul_self localMatrix
  have hB : (outsideMatrix.transpose*outsideMatrix).IsHermitian := by
    simpa using Matrix.isHermitian_conjTranspose_mul_self outsideMatrix
  have hK : ((outsideMatrix.transpose*localMatrix)*localHessian⁻¹*coupling).IsHermitian := by
    simpa [coupling] using Matrix.isHermitian_conjTranspose_mul_mul coupling hC.inv
  exact hB.sub hK

theorem schur_posSemidef : schur.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg schur_hermitian
  intro x
  change 0 ≤ dotProduct x (schur.mulVec x)
  rw [schur_energy]
  exact reducedEnergy_nonneg x

theorem schur_kernel_iff_residual (x : Outside → ℝ) :
    schur.mulVec x=0 ↔ residual x=0 := by
  constructor
  · intro h
    have he : reducedEnergy x=0 := by rw [← schur_energy,h,dotProduct_zero]
    have hs : ∑ p : Face, (residual x p)^2=0 := by
      simpa [reducedEnergy,dotProduct,pow_two] using he
    have hp := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => sq_nonneg (residual x p))).mp hs
    ext p
    have hq := hp p (Finset.mem_univ _)
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hq
  · intro h
    rw [schur_action,h,Matrix.mulVec_zero]

theorem schur_kernel_iff_closed_completion (x : Outside → ℝ) :
    schur.mulVec x=0 ↔ ∃ y : Local → ℝ,
      localMatrix.mulVec y+outsideMatrix.mulVec x=0 := by
  constructor
  · intro h
    exact ⟨response x,(schur_kernel_iff_residual x).mp h⟩
  · rintro ⟨y,hy⟩
    exact schur_closed_split x y hy

end OperatorDerivativeRewrite.Foundation.PeriodicSchurCompletedSquare
