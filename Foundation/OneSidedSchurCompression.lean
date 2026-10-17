import Foundation.OneSidedBoundaryCycles
import Foundation.OneSidedFrameGeometry

/-! A normal-equation certificate for the actual cycle-compressed Schur form. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedSchurCompression
open OneSidedBlockRank OneSidedCapComplex OneSidedBoundaryGauge OneSidedPinnedInterior
  OneSidedPhysicalProjection OneSidedCanonicalInverse OneSidedSchurForm OneSidedBoundaryCycles
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def compressed : Matrix (Fin 34) (Fin 34) ℝ := cycleMatrix.transpose*schur*cycleMatrix

def metric : Matrix (Fin 34) (Fin 34) ℝ := cycleMatrix.transpose*cycleMatrix

def candidateResidual (X : Matrix Interior (Fin 34) ℝ) : Matrix FullFace (Fin 34) ℝ :=
  fullMatrix*X+boundaryMatrix*cycleMatrix

theorem projected_response_of_normal (X : Matrix Interior (Fin 34) ℝ)
    (hn : fullMatrix.transpose*candidateResidual X=0) :
    P*X=-(M*fullCoupling*cycleMatrix) := by
  have h : fullGram*X+fullCoupling*cycleMatrix=0 := by
    simpa only [candidateResidual,Matrix.mul_add,← Matrix.mul_assoc,fullGram,fullCoupling]
      using hn
  have ht := congrArg (fun T => M*T) h
  simp only [Matrix.mul_add,← Matrix.mul_assoc,M_fullGram,Matrix.mul_zero] at ht
  exact eq_neg_of_add_eq_zero_left ht

theorem residual_of_normal (X : Matrix Interior (Fin 34) ℝ)
    (hn : fullMatrix.transpose*candidateResidual X=0) :
    candidateResidual X=boundaryMatrix*cycleMatrix-fullMatrix*M*fullCoupling*cycleMatrix := by
  calc
    _ = fullMatrix*(P*X)+boundaryMatrix*cycleMatrix := by
      rw [← Matrix.mul_assoc,fullMatrix_P]; rfl
    _ = _ := by
      rw [projected_response_of_normal X hn,Matrix.mul_neg]
      simp only [← Matrix.mul_assoc]
      abel

theorem schur_cycle_action (X : Matrix Interior (Fin 34) ℝ)
    (hn : fullMatrix.transpose*candidateResidual X=0) :
    schur*cycleMatrix=boundaryMatrix.transpose*candidateResidual X := by
  rw [residual_of_normal X hn,Matrix.mul_sub,← canonicalSchur_eq_schur]
  simp only [canonicalSchur,boundaryGram,Matrix.sub_mul,Matrix.mul_assoc,
    fullCoupling,Matrix.transpose_mul,Matrix.transpose_transpose]

theorem compressed_residual_gram (X : Matrix Interior (Fin 34) ℝ)
    (hn : fullMatrix.transpose*candidateResidual X=0) :
    compressed=(candidateResidual X).transpose*candidateResidual X := by
  symm
  calc
    _ = X.transpose*(fullMatrix.transpose*candidateResidual X)+
        cycleMatrix.transpose*(boundaryMatrix.transpose*candidateResidual X) := by
      conv_lhs => lhs; rw [candidateResidual]
      simp only [Matrix.transpose_add,Matrix.transpose_mul,Matrix.add_mul,Matrix.mul_assoc]
    _ = compressed := by
      rw [hn,Matrix.mul_zero,zero_add,← schur_cycle_action X hn]
      simp only [compressed,Matrix.mul_assoc]

theorem metric_quadratic (y : Fin 34 → ℝ) :
    dotProduct y (metric.mulVec y)=dotProduct (cycleMatrix.mulVec y) (cycleMatrix.mulVec y) := by
  rw [metric,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]

theorem compressed_quadratic (y : Fin 34 → ℝ) :
    dotProduct y (compressed.mulVec y)=
      dotProduct (cycleMatrix.mulVec y) (schur.mulVec (cycleMatrix.mulVec y)) := by
  rw [compressed,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec,dotProduct_comm]

theorem gap_transfer (delta : ℝ)
    (hc : ∀ y : Fin 34 → ℝ, delta*dotProduct y (metric.mulVec y)≤
      dotProduct y (compressed.mulVec y))
    (eta : BoundaryField) (ho : ∀ phi : Potential, dotProduct eta (boundaryGradient phi)=0) :
    delta*dotProduct eta eta≤dotProduct eta (schur.mulVec eta) := by
  obtain ⟨y,rfl⟩ := physical_representation eta ho
  simpa only [metric_quadratic,compressed_quadratic] using hc y

theorem residual_certificate_transfer (X : Matrix Interior (Fin 34) ℝ) (delta : ℝ)
    (hn : fullMatrix.transpose*candidateResidual X=0)
    (hp : ((candidateResidual X).transpose*candidateResidual X-delta • metric).PosSemidef)
    (eta : BoundaryField) (ho : ∀ phi : Potential, dotProduct eta (boundaryGradient phi)=0) :
    delta*dotProduct eta eta≤dotProduct eta (schur.mulVec eta) := by
  apply gap_transfer delta _ eta ho
  intro y
  have ht := hp.dotProduct_mulVec_nonneg y
  change 0≤dotProduct y (((candidateResidual X).transpose*candidateResidual X-delta • metric).mulVec y) at ht
  rw [← compressed_residual_gram X hn,Matrix.sub_mulVec,Matrix.smul_mulVec,
    dotProduct_sub,dotProduct_smul,smul_eq_mul] at ht
  linarith

end OperatorDerivativeRewrite.Foundation.OneSidedSchurCompression
