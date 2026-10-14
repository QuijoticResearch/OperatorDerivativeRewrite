import Foundation.GaussianWickContinuity

/-! Explicit cubic norm bounds in the actual Gaussian L2 source space. -/
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianCubicGrowth
open InfiniteGaussian IBMGaussianSteinMoments IBMCubicFirstChaos GaussianTimeSpaceHermite

theorem cube_norm_sq (h : CoefficientSpace) : ‖cube h‖^2=15*‖h‖^6 := by
  rw [← real_inner_self_eq_norm_sq,cube]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    wick_inner,real_inner_self_eq_norm_sq]
  norm_num
  simp only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,GaussianWickContinuity.wick_norm_sq]
  norm_num
  ring

theorem cube_norm_le (h : CoefficientSpace) : ‖cube h‖ ≤ 4*‖h‖^3 := by
  have hs := cube_norm_sq h
  nlinarith [norm_nonneg (cube h),pow_nonneg (norm_nonneg h) 3,sq_nonneg (‖h‖^3)]

theorem mixedCube_norm_le (u v : CoefficientSpace) (B : ℝ) (hB : 0 ≤ B)
    (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) : ‖mixedCube u v‖ ≤ 12*B^3 := by
  have hp : ‖u+v‖ ≤ 2*B := by linarith [norm_add_le u v]
  have hm : ‖u-v‖ ≤ 2*B := by linarith [norm_sub_le u v]
  have hcp : ‖cube (u+v)‖ ≤ 4*(2*B)^3 :=
    (cube_norm_le _).trans (by gcongr)
  have hcm : ‖cube (u-v)‖ ≤ 4*(2*B)^3 :=
    (cube_norm_le _).trans (by gcongr)
  have hcu : ‖cube u‖ ≤ 4*B^3 := (cube_norm_le _).trans (by gcongr)
  rw [mixedCube,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/6)]
  have ht := norm_sub_le (cube (u+v)+cube (u-v)) ((2 : ℝ) • cube u)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ht
  have ha := norm_add_le (cube (u+v)) (cube (u-v))
  nlinarith

theorem correction_norm_le (u v w : CoefficientSpace) (B : ℝ) (hB : 0 ≤ B)
    (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) (hw : ‖w‖ ≤ B) :
    ‖correction u v w‖ ≤ 18*B^3 := by
  have hm := mixedCube_norm_le u v B hB hu hv
  have hn := mixedCube_norm_le w u B hB hw hu
  rw [correction]
  have ht := norm_add_le (mixedCube u v) ((1/2 : ℝ) • mixedCube w u)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)] at ht
  nlinarith

end OperatorDerivativeRewrite.Foundation.GaussianCubicGrowth
