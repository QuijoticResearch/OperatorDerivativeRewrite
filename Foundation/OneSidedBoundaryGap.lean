import Foundation.OneSidedBoundaryPositiveData

/-! A certified0.69639 lower bound for the actual physical boundary Schur form. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedBoundaryGap
open OneSidedBlockRank OneSidedCapComplex OneSidedBoundaryGauge OneSidedBoundaryCycles
  OneSidedIntegerResponseData OneSidedCertifiedResidual OneSidedSchurCompression
  OneSidedBoundaryGramData OneSidedBoundaryPositiveData OneSidedSchurForm
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def Treal : Matrix (Fin 34) (Fin 34) ℝ := fun i j => (Tdata i j : ℝ)

def Vreal : Matrix (Fin 34) (Fin 34) ℝ := fun i j => (Vdata i j : ℝ)

def Wreal : Matrix (Fin 34) (Fin 34) ℝ := Matrix.diagonal (fun k => (weights k : ℝ))

theorem real_gram_identity (i j : Fin 34) :
    (scale : ℝ)*Treal i j=∑ k : Fin 34, Vreal i k*(weights k : ℝ)*Vreal j k := by
  simp only [Treal,Vreal]
  exact_mod_cast weighted_gram_identity i j

theorem scaled_factor : (scale : ℝ) • Treal=Vreal*Wreal*Vreal.transpose := by
  ext i j
  rw [Matrix.smul_apply,smul_eq_mul,real_gram_identity]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Wreal,Matrix.diagonal,
    Matrix.of_apply,ite_mul,mul_ite,zero_mul,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]

theorem scaled_nonnegative (y : Fin 34 → ℝ) :
    0≤dotProduct y (((scale : ℝ) • Treal).mulVec y) := by
  rw [scaled_factor,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  have he (z : Fin 34 → ℝ) : dotProduct y (Vreal.mulVec z)=
      dotProduct z (Vreal.transpose.mulVec y) := by
    simpa only [Matrix.transpose_transpose] using
      Matrix.dotProduct_transpose_mulVec Vreal.transpose y z
  rw [he]
  simp only [Wreal,Matrix.mulVec_diagonal,Pi.mul_apply,dotProduct]
  apply Finset.sum_nonneg
  intro k _
  have hw : 0≤(weights k : ℝ) := by exact_mod_cast (weights_positive k).le
  simpa only [pow_two,mul_assoc] using
    mul_nonneg hw (sq_nonneg (Vreal.transpose.mulVec y k))

theorem T_nonnegative (y : Fin 34 → ℝ) : 0≤dotProduct y (Treal.mulVec y) := by
  have hs : 0<(scale : ℝ) := by exact_mod_cast scale_positive
  have ht := scaled_nonnegative y
  rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul] at ht
  by_contra hb
  exact (not_lt_of_ge ht) (mul_neg_of_pos_of_neg hs (lt_of_not_ge hb))

theorem compressed_as_data (i j : Fin 34) :
    compressed i j=(Qdata i j : ℝ)/(denominator : ℝ) := by
  have hg : (∑ r : Fin 72, (Rnum r i : ℝ)*(Rnum r j : ℝ))=
      (denominator : ℝ)*(Qdata i j : ℝ) := by exact_mod_cast gram_identity i j
  rw [compressed_entry,hg]
  field_simp [ne_of_gt denominator_real_positive]
  <;> ring

theorem metric_as_data (i j : Fin 34) : metric i j=(Hdata i j : ℝ) := by
  rw [metric_entry]
  exact_mod_cast metric_identity i j

theorem corrected_eq : compressed-(69639/100000 : ℝ) • metric=
    (1/4825700000 : ℝ) • Treal := by
  ext i j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Treal]
  rw [compressed_as_data,metric_as_data]
  have ht : (Tdata i j : ℝ)=25000*(Qdata i j : ℝ)-69639*48257*(Hdata i j : ℝ) := by
    exact_mod_cast corrected_identity i j
  rw [ht]
  norm_num [denominator]
  <;> ring

theorem compressed_bound (y : Fin 34 → ℝ) :
    (69639/100000 : ℝ)*dotProduct y (metric.mulVec y)≤dotProduct y (compressed.mulVec y) := by
  have ht : 0≤dotProduct y ((compressed-(69639/100000 : ℝ) • metric).mulVec y) := by
    rw [corrected_eq,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
    exact mul_nonneg (by norm_num) (T_nonnegative y)
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul] at ht
  linarith

theorem boundary_gap (eta : BoundaryField)
    (ho : ∀ phi : Potential, dotProduct eta (boundaryGradient phi)=0) :
    (69639/100000 : ℝ)*dotProduct eta eta≤dotProduct eta (schur.mulVec eta) :=
  gap_transfer _ compressed_bound eta ho

theorem boundary_gap_squares (eta : BoundaryField)
    (ho : ∀ phi : Potential, dotProduct eta (boundaryGradient phi)=0) :
    (69639/100000 : ℝ)*(∑ b : Boundary, eta b^2)≤dotProduct eta (schur.mulVec eta) := by
  simpa only [dotProduct,pow_two] using boundary_gap eta ho

theorem canonical_boundary_gap (eta : BoundaryField)
    (ho : ∀ phi : Potential, dotProduct eta (boundaryGradient phi)=0) :
    (69639/100000 : ℝ)*dotProduct eta eta≤
      dotProduct eta (OneSidedCanonicalInverse.canonicalSchur.mulVec eta) := by
  rw [OneSidedCanonicalInverse.canonicalSchur_eq_schur]
  exact boundary_gap eta ho

end OperatorDerivativeRewrite.Foundation.OneSidedBoundaryGap
