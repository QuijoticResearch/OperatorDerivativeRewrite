import Foundation.PseudoClarkOconeObstruction
import Foundation.HigherHeatPolynomialRealization
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Explicit finite-core Gram degeneracy and cancellation in the source's polynomial duality argument. -/
noncomputable section
open Polynomial Matrix
open scoped Matrix NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PseudoFiniteGramObstruction
open PseudoPolynomialStein PseudoClarkOconeObstruction HigherHeatPolynomialRealization

theorem expectation_one (p : ℕ) (a : ℝ) : expectation p a 1=1 := by
  simpa only [pow_zero,moment_zero] using expectation_X_pow p 0 a

theorem expectation_C (p : ℕ) (a c : ℝ) : expectation p a (C c)=c := by
  have he : (C c : Polynomial ℝ)=c • 1 := by simp [smul_eq_C_mul]
  rw [he,map_smul,expectation_one,smul_eq_mul,mul_one]

def basis (i : Fin 2) : Polynomial ℝ := if i=0 then 1 else X

def gram (p : ℕ) (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => pairing p a (basis i) (basis j)

theorem gram_eq (p : ℕ) (hp : 2 < p) (a : ℝ) : gram p a=!![1,0;0,0] := by
  have hx := linear_mean_zero p (by omega) a
  have hxx : expectation p a (X*X)=0 := linear_square_zero p hp a
  have h1 := expectation_one p a
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [gram,basis,pairing,hx,hxx,h1]

theorem gram_det_zero (p : ℕ) (hp : 2 < p) (a : ℝ) : (gram p a).det=0 := by
  rw [gram_eq p hp a,Matrix.det_fin_two]
  norm_num

theorem gram_no_right_inverse (p : ℕ) (hp : 2 < p) (a : ℝ) :
    ¬ ∃ B : Matrix (Fin 2) (Fin 2) ℝ, gram p a*B=1 := by
  rintro ⟨B,h⟩
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul,gram_det_zero p hp a,zero_mul,Matrix.det_one] at hd
  norm_num at hd

theorem affine_radical (p : ℕ) (hp : 2 < p) (a u v : ℝ) :
    pairing p a X (u • (1:Polynomial ℝ)+v • X)=0 := by
  change expectation p a (X*(u • (1:Polynomial ℝ)+v • X))=0
  rw [mul_add,mul_smul_comm,mul_smul_comm,map_add,map_smul,map_smul,mul_one]
  have hx := linear_mean_zero p (by omega) a
  have hxx : expectation p a (X*X)=0 := linear_square_zero p hp a
  rw [hx,hxx]
  simp

theorem restricted_radical_not_full (p : ℕ) (hp : 2 < p) (a : ℝ) (ha : a ≠ 0) :
    ∃ P : Polynomial ℝ, P ≠ 0 ∧
      (∀ u v : ℝ, pairing p a P (u • (1:Polynomial ℝ)+v • X)=0) ∧
      ∃ Q : Polynomial ℝ, pairing p a P Q ≠ 0 := by
  exact ⟨X,X_ne_zero,fun u v => affine_radical p hp a u v,
    X^(p-1),linear_not_radical p (by omega) a ha⟩

def actualGram (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => kernelExpectation m hm t ht (basis i*basis j)

theorem actualGram_eq (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    actualGram m hm t ht=gram (2*m) ((-1:ℝ)^(m+1)*(t:ℝ)) := by
  ext i j
  simp only [actualGram,gram,pairing,kernelExpectation_eq_moments]

theorem actualGram_det_zero (m : ℕ) (hm : 2 ≤ m) (t : ℝ≥0) (ht : 0 < t) :
    (actualGram m (by omega) t ht).det=0 := by
  rw [actualGram_eq]
  exact gram_det_zero (2*m) (by omega) _

theorem least_probe_cancellation (p : ℕ) (hp : 0 < p) (a : ℝ) (ha : a ≠ 0) :
    ∃ P : Polynomial ℝ, P.natDegree=p ∧ P.leadingCoeff=1 ∧ expectation p a P=0 ∧
      expectation p a (X^p) ≠ 0 := by
  let P : Polynomial ℝ := X^p-C ((p.factorial:ℝ)*a)
  refine ⟨P,?_,?_,?_,?_⟩
  · exact natDegree_X_pow_sub_C
  · exact (monic_X_pow_sub_C ((p.factorial:ℝ)*a) (ne_of_gt hp)).leadingCoeff
  · dsimp only [P]
    rw [map_sub,expectation_X_pow,moment_leading p hp,expectation_C,sub_self]
  · rw [expectation_X_pow,moment_leading p hp]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero p) ha

theorem gaussian_gram_det (a : ℝ) : (gram 2 a).det=2*a := by
  have hx := linear_mean_zero 2 (by norm_num) a
  have hxx : expectation 2 a (X*X)=2*a := by
    rw [← pow_two,expectation_X_pow,moment_leading 2 (by norm_num)]
    norm_num
  rw [Matrix.det_fin_two]
  norm_num [gram,basis,pairing,expectation_one,hx,hxx]

end OperatorDerivativeRewrite.Foundation.PseudoFiniteGramObstruction
