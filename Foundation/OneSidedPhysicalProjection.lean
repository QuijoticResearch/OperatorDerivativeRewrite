import Foundation.OneSidedSchurForm

/-! The actual full interior Gram, gauge-orthogonal projection and pinned frame. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedPhysicalProjection
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank OneSidedCapComplex
  OneSidedPinnedInterior
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem matrix_eq_of_action {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B : Matrix m n ℝ) (h : ∀ v, A.mulVec v=B.mulVec v) : A=B := by
  apply Matrix.toLin'.injective
  exact LinearMap.ext h

def fullMap : Field →ₗ[ℝ] (FullFace → ℝ) := flatten.toLinearMap.comp incidence

def fullMatrix : Matrix FullFace Interior ℝ := LinearMap.toMatrix' fullMap

def fullGram : Matrix Interior Interior ℝ := fullMatrix.transpose*fullMatrix

def liftMatrix : Matrix Interior Free ℝ := LinearMap.toMatrix' lift

def pinMatrix : Matrix Free Interior ℝ := LinearMap.toMatrix' pin

def P : Matrix Interior Interior ℝ := 1-(1/4 : ℝ) • Matrix.vecMulVec gauge gauge

def W : Matrix Interior Free ℝ := P*liftMatrix

theorem fullMatrix_mulVec (f : Field) : fullMatrix.mulVec f=fullMap f :=
  LinearMap.toMatrix'_mulVec _ _

theorem liftMatrix_mulVec (y : FreeField) : liftMatrix.mulVec y=lift y :=
  LinearMap.toMatrix'_mulVec _ _

theorem pinMatrix_mulVec (f : Field) : pinMatrix.mulVec f=pin f :=
  LinearMap.toMatrix'_mulVec _ _

theorem fullMatrix_inner (p : Inner) (e : Interior) :
    fullMatrix (.inl p) e=OneSidedGramSector.innerMatrix p e := rfl

theorem fullMatrix_upper (p : Upper) (e : Interior) :
    fullMatrix (.inr p) e=OneSidedGramSector.upperMatrix p e := rfl

theorem fullGram_eq_gram : fullGram=OneSidedGramSector.gram := by
  ext e f
  simp only [fullGram,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_sum_type,
    fullMatrix_inner,fullMatrix_upper,OneSidedGramSector.gram,Matrix.add_apply,
    Matrix.mul_apply,Matrix.transpose_apply]

theorem fullMatrix_lift : fullMatrix*liftMatrix=localMatrix := by
  classical
  apply matrix_eq_of_action
  intro y
  rw [← Matrix.mulVec_mulVec,fullMatrix_mulVec,liftMatrix_mulVec,localMatrix_mulVec]
  rfl

theorem fullMatrix_gauge : fullMatrix.mulVec gauge=0 := by
  rw [fullMatrix_mulVec]
  change flatten (incidence gauge)=0
  rw [gauge_incidence_zero,map_zero]

theorem fullGram_gauge : fullGram.mulVec gauge=0 := by
  rw [fullGram,← Matrix.mulVec_mulVec,fullMatrix_gauge,Matrix.mulVec_zero]

theorem gauge_norm : dotProduct gauge gauge=4 := by
  have h := originField_norm_sq
  rw [Finset.sum_subtype (F := (inferInstance : Fintype Interior))
    (p := fun e : EdgeData => e∈edges) edges (fun _ => Iff.rfl)] at h
  simpa only [dotProduct,OneSidedBlockRank.gauge,pow_two] using h

theorem P_action (f : Field) : P.mulVec f=f-(dotProduct f gauge/4) • gauge := by
  have ho : (Matrix.vecMulVec gauge gauge).mulVec f=dotProduct f gauge • gauge := by
    funext e
    change (∑ i : Interior, gauge e*gauge i*f i)=(∑ i : Interior, f i*gauge i)*gauge e
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [P,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,ho,smul_smul]
  funext e
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem P_gauge : P.mulVec gauge=0 := by
  rw [P_action,gauge_norm]
  norm_num

theorem P_pairing (f : Field) : dotProduct (P.mulVec f) gauge=0 := by
  rw [P_action,sub_dotProduct,smul_dotProduct,smul_eq_mul,gauge_norm]
  ring

theorem P_idempotent : P*P=P := by
  apply matrix_eq_of_action
  intro f
  rw [← Matrix.mulVec_mulVec,P_action,P_pairing]
  simp

theorem P_transpose : P.transpose=P := by
  ext e f
  simp [P,Matrix.transpose_apply,Matrix.one_apply,Matrix.vecMulVec_apply,eq_comm,mul_comm]

theorem fullGram_transpose : fullGram.transpose=fullGram := by
  simp [fullGram,Matrix.transpose_mul]

theorem fullMatrix_P : fullMatrix*P=fullMatrix := by
  classical
  apply matrix_eq_of_action
  intro f
  rw [← Matrix.mulVec_mulVec,P_action,Matrix.mulVec_sub,Matrix.mulVec_smul,
    fullMatrix_gauge,smul_zero,sub_zero]

theorem fullGram_P : fullGram*P=fullGram := by
  rw [fullGram,Matrix.mul_assoc,fullMatrix_P]

theorem P_fullGram : P*fullGram=fullGram := by
  have h := congrArg Matrix.transpose fullGram_P
  simpa only [Matrix.transpose_mul,fullGram_transpose,P_transpose] using h

theorem W_pin : W*pinMatrix=P := by
  apply matrix_eq_of_action
  intro f
  rw [W,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,liftMatrix_mulVec,pinMatrix_mulVec,
    lift_pin,Matrix.mulVec_sub,Matrix.mulVec_smul,P_gauge,smul_zero,sub_zero]

theorem pinned_Gram : liftMatrix.transpose*fullGram*liftMatrix=localGram := by
  calc
    _ = (fullMatrix*liftMatrix).transpose*(fullMatrix*liftMatrix) := by
      simp only [fullGram,Matrix.transpose_mul,Matrix.mul_assoc]
    _ = localGram := by rw [fullMatrix_lift]; rfl

theorem physical_Gram : W.transpose*fullGram*W=localGram := by
  calc
    _ = liftMatrix.transpose*(P*fullGram*P)*liftMatrix := by
      simp only [W,Matrix.transpose_mul,P_transpose,Matrix.mul_assoc]
    _ = liftMatrix.transpose*fullGram*liftMatrix := by rw [P_fullGram,fullGram_P]
    _ = localGram := pinned_Gram

end OperatorDerivativeRewrite.Foundation.OneSidedPhysicalProjection
