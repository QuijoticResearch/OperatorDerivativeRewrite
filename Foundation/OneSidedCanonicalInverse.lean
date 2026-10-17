import Foundation.OneSidedPhysicalProjection

/-! A canonical Moore–Penrose matrix and agreement with pinned Schur elimination. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedCanonicalInverse
open OneSidedBlockRank OneSidedCapComplex OneSidedPinnedInterior
  OneSidedPhysicalProjection OneSidedSchurForm
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def M : Matrix Interior Interior ℝ := W*localGram⁻¹*W.transpose

theorem inverse_left : localGram⁻¹*localGram=1 :=
  Matrix.nonsing_inv_mul _ (localGram.isUnit_iff_isUnit_det.mp localGram_isUnit)

theorem M_fullGram_W : M*fullGram*W=W := by
  calc
    _ = W*localGram⁻¹*(W.transpose*fullGram*W) := by
      simp only [M,Matrix.mul_assoc]
    _ = W := by rw [physical_Gram,Matrix.mul_assoc,inverse_left,Matrix.mul_one]

theorem M_fullGram : M*fullGram=P := by
  calc
    _ = M*fullGram*P := by rw [Matrix.mul_assoc,fullGram_P]
    _ = M*fullGram*(W*pinMatrix) := by rw [W_pin]
    _ = P := by rw [← Matrix.mul_assoc,M_fullGram_W,W_pin]

theorem M_hermitian : M.IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_mul W.transpose
    (Matrix.isHermitian_conjTranspose_mul_self localMatrix).inv
  simpa [M,localGram] using h

theorem M_transpose : M.transpose=M := by
  simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using M_hermitian

theorem fullGram_M : fullGram*M=P := by
  have h := congrArg Matrix.transpose M_fullGram
  simpa only [Matrix.transpose_mul,fullGram_transpose,M_transpose,P_transpose] using h

theorem P_W : P*W=W := by
  rw [W,← Matrix.mul_assoc,P_idempotent]

theorem P_M : P*M=M := by
  rw [M,← Matrix.mul_assoc,← Matrix.mul_assoc,P_W]

theorem penrose_first : fullGram*M*fullGram=fullGram := by
  rw [fullGram_M,P_fullGram]

theorem penrose_second : M*fullGram*M=M := by
  rw [M_fullGram,P_M]

theorem penrose_third : (fullGram*M).transpose=fullGram*M := by
  rw [fullGram_M,P_transpose]

theorem penrose_fourth : (M*fullGram).transpose=M*fullGram := by
  rw [M_fullGram,P_transpose]

def fullCoupling : Matrix Interior Boundary ℝ := fullMatrix.transpose*boundaryMatrix

def canonicalSchur : Matrix Boundary Boundary ℝ :=
  boundaryGram-fullCoupling.transpose*M*fullCoupling

theorem P_fullTranspose : P*fullMatrix.transpose=fullMatrix.transpose := by
  have h := congrArg Matrix.transpose fullMatrix_P
  simpa only [Matrix.transpose_mul,P_transpose] using h

theorem W_coupling : W.transpose*fullCoupling=coupling := by
  calc
    _ = liftMatrix.transpose*(P*fullMatrix.transpose)*boundaryMatrix := by
      simp only [W,fullCoupling,Matrix.transpose_mul,P_transpose,Matrix.mul_assoc]
    _ = (fullMatrix*liftMatrix).transpose*boundaryMatrix := by
      rw [P_fullTranspose]; simp only [Matrix.transpose_mul,Matrix.mul_assoc]
    _ = coupling := by rw [fullMatrix_lift]; rfl

theorem canonicalSchur_eq_schur : canonicalSchur=schur := by
  have ht := congrArg Matrix.transpose W_coupling
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose] at ht
  calc
    _ = boundaryGram-(fullCoupling.transpose*W)*localGram⁻¹*
        (W.transpose*fullCoupling) := by
      simp only [canonicalSchur,M,Matrix.mul_assoc]
    _ = schur := by rw [ht,W_coupling]; rfl

end OperatorDerivativeRewrite.Foundation.OneSidedCanonicalInverse
