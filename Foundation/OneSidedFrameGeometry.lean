import Foundation.OneSidedMinimumNorm
import Foundation.OneSidedPhysicalGap
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Exact Euclidean geometry of the projected pinned frame. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedFrameGeometry
open OneSidedBlockRank OneSidedPinnedInterior OneSidedPhysicalProjection
  OneSidedCanonicalInverse OneSidedPhysicalGap
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def h : FreeField := fun e => gauge e.val

def G : Matrix Free Free ℝ := W.transpose*W

theorem sum_free (f : Interior → ℝ) : (∑ e : Free, f e.val)+f pole=∑ e : Interior, f e := by
  have ht := Finset.sum_erase_add Finset.univ f (Finset.mem_univ pole)
  rw [Finset.sum_subtype (F := (inferInstance : Fintype Free))
    (p := fun e : Interior => e≠pole) (Finset.univ.erase pole) (by simp)] at ht
  exact ht

theorem h_norm : dotProduct h h=3 := by
  have ht := sum_free (fun e => gauge e*gauge e)
  change dotProduct h h+gauge pole*gauge pole=dotProduct gauge gauge at ht
  rw [gauge_pole,gauge_norm] at ht
  linarith

theorem lift_pairing (y : FreeField) (f : Field) :
    dotProduct (lift y) f=dotProduct y (fun e : Free => f e.val) := by
  have ht := sum_free (fun e => lift y e*f e)
  simp only [lift_free,lift_pole,zero_mul,add_zero] at ht
  exact ht.symm

theorem lift_norm (y : FreeField) : dotProduct (lift y) (lift y)=dotProduct y y := by
  rw [lift_pairing]
  simp only [lift_free]

theorem lift_gauge_pairing (y : FreeField) : dotProduct (lift y) gauge=dotProduct y h :=
  lift_pairing y gauge

theorem liftTranspose_action (f : Field) :
    liftMatrix.transpose.mulVec f=fun e : Free => f e.val := by
  funext e
  have ht := Matrix.dotProduct_transpose_mulVec liftMatrix (Pi.single e 1) f
  rw [liftMatrix_mulVec,dotProduct_comm f,lift_pairing] at ht
  simpa only [single_dotProduct,one_mul] using ht

theorem G_compression : G=liftMatrix.transpose*P*liftMatrix := by
  calc
    _ = liftMatrix.transpose*(P*P)*liftMatrix := by
      simp only [G,W,Matrix.transpose_mul,P_transpose,Matrix.mul_assoc]
    _ = _ := by rw [P_idempotent]

theorem G_action (y : FreeField) : G.mulVec y=y-(dotProduct y h/4) • h := by
  rw [G_compression,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,liftMatrix_mulVec,
    liftTranspose_action,P_action,lift_gauge_pairing]
  funext e
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,lift_free,h]

theorem G_formula : G=1-(1/4 : ℝ) • Matrix.vecMulVec h h := by
  apply matrix_eq_of_action
  intro y
  rw [G_action,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec,dotProduct_comm h y]
  funext e
  simp only [Pi.sub_apply,Pi.smul_apply,op_smul_eq_mul,smul_eq_mul]
  ring

theorem G_quadratic (y : FreeField) : dotProduct y (G.mulVec y)=
    dotProduct y y-(dotProduct y h)^2/4 := by
  rw [G_action,dotProduct_sub,dotProduct_smul,smul_eq_mul]
  ring

theorem frame_norm (y : FreeField) : dotProduct (W.mulVec y) (W.mulVec y)=
    dotProduct y y-(dotProduct y h)^2/4 := by
  rw [← Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec]
  exact G_quadratic y

theorem frame_gauge_norm : dotProduct (W.mulVec h) (W.mulVec h)=3/4 := by
  rw [frame_norm,h_norm]
  norm_num

theorem pairing_bound (y : FreeField) : (dotProduct y h)^2≤3*dotProduct y y := by
  have ht := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y h
  have hn : (∑ e : Free, h e^2)=3 := by simpa only [dotProduct,pow_two] using h_norm
  simp only [hn,mul_comm] at ht
  simpa only [dotProduct,pow_two] using ht

theorem frame_norm_lower (y : FreeField) :
    (1/4 : ℝ)*dotProduct y y≤dotProduct (W.mulVec y) (W.mulVec y) := by
  rw [frame_norm]
  have ht := pairing_bound y
  linarith

theorem frame_norm_upper (y : FreeField) :
    dotProduct (W.mulVec y) (W.mulVec y)≤dotProduct y y := by
  rw [frame_norm]
  nlinarith [sq_nonneg (dotProduct y h)]

theorem G_determinant : G.det=1/4 := by
  have hm : G=1+Matrix.replicateCol Unit (-(1/4 : ℝ) • h)*Matrix.replicateRow Unit h := by
    rw [← Matrix.vecMulVec_eq]
    rw [G_formula]
    ext e f
    simp [Matrix.vecMulVec_apply]
    ring
  rw [hm,Matrix.det_one_add_replicateCol_mul_replicateRow,dotProduct_smul,smul_eq_mul,h_norm]
  norm_num

theorem pinned_quantitative_bound (y : FreeField) :
    (6893/40000 : ℝ)*dotProduct y y≤
      OneSidedBlockIncidence.realEnergy (extend (lift y)) := by
  have ht := projected_energy_lower_bound (lift y)
  rw [lift_norm,lift_gauge_pairing] at ht
  have hb := pairing_bound y
  norm_num [delta] at ht
  linarith

end OperatorDerivativeRewrite.Foundation.OneSidedFrameGeometry
