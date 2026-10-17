import Foundation.SparseBlockWilsonAction

/-! No fixed quadratic relative error works locally, even after fixed angle rescaling. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.SparseBlockRelativeObstruction
set_option backward.isDefEq.respectTransparency false
open SparseWilsonCurvature SparseBlockWilsonAction SU2OrderedLinkHessian

def relativeLower (C a θ : ℝ) : ℝ :=
  Real.sin (a*θ)/(a*θ)*(10/4)-C*(a*θ)^2*2

theorem arbitrary_constant_violation (C a ε : ℝ) (hC : 0 ≤ C) (ha : 0 < a) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < ε ∧
      deriv (deriv (blockAction θ)) 0 < relativeLower C a θ := by
  let K : ℝ := 2*C*a^2+(5/12)*a^2+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨θ, ht, htε, hc⟩ := correction_exceeds_quadratic K ε hK hε
  have hp : 0 < a*θ := mul_pos ha ht
  have hs := Real.sin_ge_sub_cube hp.le
  have hdiv : 1-(a*θ)^2/6 ≤ Real.sin (a*θ)/(a*θ) := by
    apply (le_div_iff₀ hp).2
    nlinarith
  have hcos := Real.cos_le_one θ
  rw [correction_eq] at hc
  refine ⟨θ, ht, htε, ?_⟩
  rw [blockAction_second_derivative]
  unfold curvatureValue relativeLower
  dsimp [K] at hc
  nlinarith

theorem no_local_relative_bound (a : ℝ) (ha : 0 < a) :
    ¬ ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ θ : ℝ, 0 < θ → θ < ε →
      relativeLower C a θ ≤ deriv (deriv (blockAction θ)) 0 := by
  rintro ⟨C, ε, hC, hε, hb⟩
  obtain ⟨θ, ht, htε, hv⟩ := arbitrary_constant_violation C a ε hC ha hε
  exact (not_lt_of_ge (hb θ ht htε)) hv

theorem rational_slack_three :
    deriv (deriv (blockAction witnessAngle)) 0 < relativeLower 9 3 witnessAngle := by
  rw [blockAction_second_derivative]
  have hs := Real.sin_ge_sub_cube (show 0 ≤ witnessAngle by norm_num [witnessAngle])
  have hs3 := Real.sin_ge_sub_cube (show 0 ≤ 3*witnessAngle by norm_num [witnessAngle])
  have hc := Real.cos_le_one witnessAngle
  norm_num [witnessAngle] at hs hs3 hc
  norm_num [curvatureValue, relativeLower, witnessAngle]
  linarith

end OperatorDerivativeRewrite.Foundation.SparseBlockRelativeObstruction
