import Foundation.RestrictedEulerAlignedGrowth
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The self-similar RE family has a fixed full-matrix spectral polynomial
while its symmetric-strain spectrum varies with its nonnormal geometry. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RestrictedEulerSpectralDistinction
open RestrictedEulerRatioCounterexample RestrictedEulerAlignedGrowth
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

theorem shifted_determinant (p a r : ℝ) (ha : a^2=(p-2)*(p+1)) :
    (r • (1 : Matrix (Fin 3) (Fin 3) ℝ)-matrix p a).det=(r-1)^2*(r+2) := by
  calc
    (r • (1 : Matrix (Fin 3) (Fin 3) ℝ)-matrix p a).det=
        (r-1)*((r+p)*(r-p+1)+a^2) := by
      rw [Matrix.det_fin_three]
      norm_num [matrix] <;> ring
    _ = (r-1)^2*(r+2) := by rw [ha]; ring

theorem shifted_isUnit_iff (p a r : ℝ) (ha : a^2=(p-2)*(p+1)) :
    IsUnit (r • (1 : Matrix (Fin 3) (Fin 3) ℝ)-matrix p a) ↔ r ≠ 1 ∧ r ≠ -2 := by
  rw [Matrix.isUnit_iff_isUnit_det,shifted_determinant p a r ha]
  simp [isUnit_iff_ne_zero,sub_eq_zero,add_eq_zero_iff_eq_neg]

theorem spectral_parameter_iff (p a r : ℝ) (ha : a^2=(p-2)*(p+1)) :
    ¬ IsUnit (r • (1 : Matrix (Fin 3) (Fin 3) ℝ)-matrix p a) ↔ r=1 ∨ r=-2 := by
  rw [shifted_isUnit_iff p a r ha]
  tauto

theorem same_full_spectral_set (p a q b r : ℝ)
    (ha : a^2=(p-2)*(p+1)) (hb : b^2=(q-2)*(q+1)) :
    IsUnit (r • (1 : Matrix (Fin 3) (Fin 3) ℝ)-matrix p a) ↔
      IsUnit (r • (1 : Matrix (Fin 3) (Fin 3) ℝ)-matrix q b) := by
  rw [shifted_isUnit_iff p a r ha,shifted_isUnit_iff q b r hb]

theorem profile_polynomial (p a : ℝ) (ha : a^2=(p-2)*(p+1)) :
    matrix p a*matrix p a+matrix p a=(2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h := self_similar_profile p a ha
  unfold flow at h
  rw [trace_square p a ha] at h
  norm_num at h
  calc
    matrix p a*matrix p a+matrix p a=
        matrix p a*matrix p a+(-(matrix p a*matrix p a)+(2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) :=
      congrArg (fun X => matrix p a*matrix p a+X) h.symm
    _ = _ := by abel

theorem nonnormal (p a : ℝ) (hp : 2 < p) (ha : a ≠ 0) :
    (matrix p a).transpose*matrix p a ≠ matrix p a*(matrix p a).transpose := by
  intro h
  have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 2) h
  change (∑ k, matrix p a k 0*matrix p a k 2)=
    ∑ k, matrix p a 0 k*matrix p a 2 k at he
  norm_num [matrix,Fin.sum_univ_succ] at he
  have hz : a*(2*p-1)=0 := by nlinarith [he]
  exact (mul_ne_zero ha (by linarith : 2*p-1 ≠ 0)) hz

theorem proposed_profile_nonnormal :
    (matrix 4 (Real.sqrt 10)).transpose*matrix 4 (Real.sqrt 10) ≠
      matrix 4 (Real.sqrt 10)*(matrix 4 (Real.sqrt 10)).transpose :=
  nonnormal 4 (Real.sqrt 10) (by norm_num) sqrt_ten_nonzero

end OperatorDerivativeRewrite.Foundation.RestrictedEulerSpectralDistinction
