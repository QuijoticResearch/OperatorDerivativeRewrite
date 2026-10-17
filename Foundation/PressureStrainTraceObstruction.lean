import Foundation.AffineStretchingPressureBalance

/-! A local algebraic trace obstruction in the displayed manuscript strain
formula, and trace-consistent full/trace-free pressure conventions. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PressureStrainTraceObstruction
open RestrictedEulerRatioCounterexample AffineStretchingPressureBalance
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def frobeniusSquared (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ∑ i, ∑ j, (A i j)^2

theorem vorticity_trace_identity (A : Matrix (Fin 3) (Fin 3) ℝ) :
    dotProduct (vorticity A) (vorticity A)+Matrix.trace (A*A)=frobeniusSquared A := by
  simp [frobeniusSquared,vorticity,dotProduct,Matrix.trace,Matrix.diag,Matrix.mul_apply,
    Fin.sum_univ_succ] <;> ring

theorem frobeniusSquared_nonneg (A : Matrix (Fin 3) (Fin 3) ℝ) :
    0 ≤ frobeniusSquared A :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

theorem frobeniusSquared_zero_iff (A : Matrix (Fin 3) (Fin 3) ℝ) :
    frobeniusSquared A=0 ↔ A=0 := by
  constructor
  · intro h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))).mp h
    ext i j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (A i j))).mp
      (hi i (Finset.mem_univ _))
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp (hj j (Finset.mem_univ _))
  · intro h
    simp [h,frobeniusSquared]

theorem frobeniusSquared_pos (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ≠ 0) :
    0 < frobeniusSquared A := by
  have hn := frobeniusSquared_nonneg A
  have hz : frobeniusSquared A ≠ 0 := fun h => hA ((frobeniusSquared_zero_iff A).mp h)
  rcases eq_or_lt_of_le hn with h | h
  · exact False.elim (hz h.symm)
  · exact h

theorem source_trace_under_poisson (A P : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : -Matrix.trace P=Matrix.trace (A*A)) :
    Matrix.trace (sourceStrainRHS A P)=frobeniusSquared A := by
  rw [source_trace_general]
  have h := vorticity_trace_identity A
  linarith

theorem source_positive_trace (A P : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ≠ 0)
    (hP : -Matrix.trace P=Matrix.trace (A*A)) : 0 < Matrix.trace (sourceStrainRHS A P) := by
  rw [source_trace_under_poisson A P hP]
  exact frobeniusSquared_pos A hA

theorem source_traceless_iff (A P : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : -Matrix.trace P=Matrix.trace (A*A)) :
    Matrix.trace (sourceStrainRHS A P)=0 ↔ A=0 := by
  rw [source_trace_under_poisson A P hP,frobeniusSquared_zero_iff]

theorem traceless_correction_trace (A P D : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : -Matrix.trace P=Matrix.trace (A*A)) (hD : Matrix.trace D=0) :
    Matrix.trace (sourceStrainRHS A P+D)=frobeniusSquared A := by
  rw [Matrix.trace_add,source_trace_under_poisson A P hP,hD,add_zero]

theorem no_traceless_repair (A P D : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ≠ 0)
    (hP : -Matrix.trace P=Matrix.trace (A*A)) (hD : Matrix.trace D=0) :
    Matrix.trace (sourceStrainRHS A P+D) ≠ 0 := by
  rw [traceless_correction_trace A P D hP hD]
  exact fun h => hA ((frobeniusSquared_zero_iff A).mp h)

theorem symmetric_skew_square_trace (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (A*A)=Matrix.trace (strain A*strain A)+
      Matrix.trace ((A-strain A)*(A-strain A)) := by
  simp [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.sub_apply,strain,
    Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul,
    Fin.sum_univ_succ] <;> ring

def fullStrainRHS (A P : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  -(strain A*strain A)-(A-strain A)*(A-strain A)-P

def traceFreeStrainRHS (A P : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fullStrainRHS A P+
    ((Matrix.trace (strain A*strain A)-dotProduct (vorticity A) (vorticity A)/2)/3) • 1

theorem full_trace (A P : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (fullStrainRHS A P)=-Matrix.trace (A*A)-Matrix.trace P := by
  simp only [fullStrainRHS,Matrix.trace_sub,Matrix.trace_neg]
  rw [symmetric_skew_square_trace A]
  ring

theorem full_trace_zero_iff_poisson (A P : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (fullStrainRHS A P)=0 ↔ -Matrix.trace P=Matrix.trace (A*A) := by
  rw [full_trace]
  constructor <;> intro h <;> linarith

theorem traceFree_trace (A P : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (traceFreeStrainRHS A P)=-Matrix.trace P := by
  simp only [traceFreeStrainRHS,fullStrainRHS,Matrix.trace_add,Matrix.trace_sub,
    Matrix.trace_neg,Matrix.trace_smul]
  rw [skew_trace_identity]
  have hI : Matrix.trace (1 : Matrix (Fin 3) (Fin 3) ℝ)=3 := by
    norm_num [Matrix.trace,Matrix.diag,Fin.sum_univ_succ]
  rw [hI]
  ring

theorem traceFree_trace_zero_iff (A P : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (traceFreeStrainRHS A P)=0 ↔ Matrix.trace P=0 := by
  rw [traceFree_trace,neg_eq_zero]

end OperatorDerivativeRewrite.Foundation.PressureStrainTraceObstruction
