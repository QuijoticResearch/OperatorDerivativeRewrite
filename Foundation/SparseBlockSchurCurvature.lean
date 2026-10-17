import Foundation.SparseBlockPartialHessian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The actual sparse SU(2) Hessian has a quadratically stable scalar Schur complement. -/
noncomputable section
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.SparseBlockSchurCurvature
set_option backward.isDefEq.respectTransparency false
open SparseBlockPartialHessian ChristoffelSkewCancellation

def diagonal (θ : ℝ) : ℝ := (4+Real.cos θ)/4
def mixed (θ : ℝ) : ℝ := -Real.sin θ/4
def schur (θ : ℝ) : ℝ := partialHessian θ 0 0 -
  partialHessian θ 0 1*partialHessian θ 1 0/partialHessian θ 1 1

theorem diagonal_lower (θ : ℝ) : (3/4 : ℝ) ≤ diagonal θ := by
  unfold diagonal
  linarith [Real.neg_one_le_cos θ]

theorem diagonal_pos (θ : ℝ) : 0 < diagonal θ := lt_of_lt_of_le (by norm_num) (diagonal_lower θ)

theorem schur_eq (θ : ℝ) : schur θ=diagonal θ-(mixed θ)^2/diagonal θ := by
  simp [schur, partialHessian_eq, diagonal, mixed, pow_two]

theorem schur_cos_form (θ : ℝ) :
    schur θ=(15+8*Real.cos θ+2*(Real.cos θ)^2)/(4*(4+Real.cos θ)) := by
  have hd : 4+Real.cos θ ≠ 0 := by linarith [Real.neg_one_le_cos θ]
  rw [schur_eq]
  unfold diagonal mixed
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem schur_lower_factor (θ : ℝ) :
    schur θ-3/4=(Real.cos θ+1)*(2*Real.cos θ+3)/(4*(4+Real.cos θ)) := by
  have hd : 4+Real.cos θ ≠ 0 := by linarith [Real.neg_one_le_cos θ]
  rw [schur_cos_form]
  field_simp
  ring

theorem schur_deficit_factor (θ : ℝ) :
    5/4-schur θ=(1-Real.cos θ)*((2*Real.cos θ+5)/(4*(4+Real.cos θ))) := by
  have hd : 4+Real.cos θ ≠ 0 := by linarith [Real.neg_one_le_cos θ]
  rw [schur_cos_form]
  field_simp
  ring

theorem schur_lower (θ : ℝ) : (3/4 : ℝ) ≤ schur θ := by
  have hc := Real.neg_one_le_cos θ
  have hn : 0 ≤ (Real.cos θ+1)*(2*Real.cos θ+3)/(4*(4+Real.cos θ)) := by
    apply div_nonneg
    · apply mul_nonneg <;> linarith
    · linarith
  rw [← schur_lower_factor] at hn
  linarith

theorem schur_upper (θ : ℝ) : schur θ ≤ 5/4 := by
  have hc := Real.neg_one_le_cos θ
  have hn : 0 ≤ (1-Real.cos θ)*((2*Real.cos θ+5)/(4*(4+Real.cos θ))) := by
    apply mul_nonneg
    · linarith [Real.cos_le_one θ]
    · apply div_nonneg <;> linarith
  rw [← schur_deficit_factor] at hn
  linarith

theorem schur_quadratic_loss (θ : ℝ) : 5/4-schur θ ≤ 7*θ^2/40 := by
  have hd : 0 < 4*(4+Real.cos θ) := by linarith [Real.neg_one_le_cos θ]
  have hr : (2*Real.cos θ+5)/(4*(4+Real.cos θ)) ≤ (7/20 : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    linarith [Real.cos_le_one θ]
  rw [schur_deficit_factor]
  calc
    _ ≤ (1-Real.cos θ)*(7/20) :=
      mul_le_mul_of_nonneg_left hr (by linarith [Real.cos_le_one θ])
    _ ≤ (θ^2/2)*(7/20) := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
    _ = _ := by ring

theorem schur_zero : schur 0=5/4 := by rw [schur_cos_form]; norm_num

theorem schur_pi : schur Real.pi=3/4 := by rw [schur_cos_form]; norm_num

theorem schur_derivative_zero : HasDerivAt schur 0 0 := by
  have hc : HasDerivAt Real.cos 0 0 := by simpa using Real.hasDerivAt_cos 0
  have hn : HasDerivAt (fun θ : ℝ => 15+8*Real.cos θ+2*(Real.cos θ)^2) 0 0 := by
    have hh := ((hc.const_mul 8).const_add 15).add ((hc.pow 2).const_mul 2)
    change HasDerivAt (fun θ : ℝ => 15+8*Real.cos θ+2*(Real.cos θ)^2)
      (8*0+2*(2*Real.cos 0^(2-1)*0)) 0 at hh
    simpa only [mul_zero, zero_add, add_zero] using hh
  have hd : HasDerivAt (fun θ : ℝ => 4*(4+Real.cos θ)) 0 0 := by
    simpa using (hc.const_add 4).const_mul 4
  have he : schur=(fun θ : ℝ => (15+8*Real.cos θ+2*(Real.cos θ)^2)/(4*(4+Real.cos θ))) :=
    funext schur_cos_form
  rw [he]
  have hh := hn.div hd (by norm_num : 4*(4+Real.cos 0) ≠ 0)
  change HasDerivAt (fun θ : ℝ => (15+8*Real.cos θ+2*(Real.cos θ)^2)/(4*(4+Real.cos θ)))
    ((0*(4*(4+Real.cos 0))-(15+8*Real.cos 0+2*(Real.cos 0)^2)*0)/(4*(4+Real.cos 0))^2) 0 at hh
  simpa only [zero_mul, mul_zero, sub_zero, zero_div] using hh

theorem actual_hessian_completed_square (θ x y : ℝ) :
    contraction (partialHessian θ) ![x,y] ![x,y] =
      schur θ*x^2+diagonal θ*(y+mixed θ/diagonal θ*x)^2 := by
  have hd := ne_of_gt (diagonal_pos θ)
  have hm : partialHessian θ=!![diagonal θ,mixed θ;mixed θ,diagonal θ] := by
    rw [partialHessian_eq]
    rfl
  rw [hm, schur_eq]
  norm_num [contraction, Fin.sum_univ_two]
  field_simp
  ring

theorem actual_hessian_schur_bound (θ x y : ℝ) :
    schur θ*x^2 ≤ contraction (partialHessian θ) ![x,y] ![x,y] := by
  rw [actual_hessian_completed_square]
  exact le_add_of_nonneg_right (mul_nonneg (le_of_lt (diagonal_pos θ)) (sq_nonneg _))

theorem actual_hessian_minimum (θ x : ℝ) :
    contraction (partialHessian θ) ![x,-mixed θ/diagonal θ*x]
      ![x,-mixed θ/diagonal θ*x]=schur θ*x^2 := by
  rw [actual_hessian_completed_square]
  have he : -mixed θ/diagonal θ*x+mixed θ/diagonal θ*x=0 := by ring
  rw [he]
  simp

theorem actual_hessian_quadratic_schur_bound (θ x y : ℝ) :
    (5/4-7*θ^2/40)*x^2 ≤ contraction (partialHessian θ) ![x,y] ![x,y] := by
  have hs : 5/4-7*θ^2/40 ≤ schur θ := by linarith [schur_quadratic_loss θ]
  exact (mul_le_mul_of_nonneg_right hs (sq_nonneg x)).trans (actual_hessian_schur_bound θ x y)

end OperatorDerivativeRewrite.Foundation.SparseBlockSchurCurvature
