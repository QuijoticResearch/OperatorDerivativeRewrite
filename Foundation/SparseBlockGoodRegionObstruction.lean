import Foundation.SparseBlockRelativeObstruction
import Foundation.SU2ExplicitRotationLog

/-! Strict diagonal-principal-log caps and incompatible relative-error assumptions. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.SparseBlockGoodRegionObstruction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
open SparseBlockRelativeObstruction SparseBlockWilsonAction SU2ExplicitRotationLog

theorem arbitrarily_small_strict_region (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < ε ∧ 3*θ < Real.pi/2 ∧
      (∀ p∈faces, diagonalLogLength (evalWord θ 0 (faceWord p)) < 3*θ) ∧
      deriv (deriv (blockAction θ)) 0 < relativeLower C 3 θ := by
  have he : 0 < min ε (Real.pi/6) := lt_min hε (by positivity)
  obtain ⟨θ, ht, htmin, hv⟩ := arbitrary_constant_violation C 3 (min ε (Real.pi/6))
    hC (by norm_num) he
  have htε : θ < ε := lt_of_lt_of_le htmin (min_le_left _ _)
  have htπ6 : θ < Real.pi/6 := lt_of_lt_of_le htmin (min_le_right _ _)
  have htπ : θ < Real.pi := by linarith [Real.pi_pos]
  refine ⟨θ, ht, htε, by linarith, ?_, hv⟩
  intro p hp
  exact base_logLength_strict θ ht htπ p hp

theorem error_split_contradiction (C a θ chr met : ℝ)
    (hv : deriv (deriv (blockAction θ)) 0 < relativeLower C a θ)
    (htotal : chr+met=deriv (deriv (blockAction θ)) 0-10/4)
    (hchr : chr=0)
    (hmet : (Real.sin (a*θ)/(a*θ)-1)*(10/4)-C*(a*θ)^2*2 ≤ met) : False := by
  unfold relativeLower at hv
  linarith

theorem no_uniform_zero_chr_split :
    ¬ ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ θ : ℝ, 0 < θ → θ < ε →
      ∃ chr met : ℝ, chr+met=deriv (deriv (blockAction θ)) 0-10/4 ∧ chr=0 ∧
        (Real.sin (3*θ)/(3*θ)-1)*(10/4)-C*(3*θ)^2*2 ≤ met := by
  rintro ⟨C, ε, hC, hε, hb⟩
  obtain ⟨θ, ht, htε, _, _, hv⟩ := arbitrarily_small_strict_region C ε hC hε
  obtain ⟨chr, met, htotal, hchr, hmet⟩ := hb θ ht htε
  exact error_split_contradiction C 3 θ chr met hv htotal hchr hmet

theorem rational_strict_configuration :
    3*SparseWilsonCurvature.witnessAngle < Real.pi/2 ∧
      (∀ p∈faces, diagonalLogLength
        (evalWord SparseWilsonCurvature.witnessAngle 0 (faceWord p)) <
          3*SparseWilsonCurvature.witnessAngle) ∧
      deriv (deriv (blockAction SparseWilsonCurvature.witnessAngle)) 0 <
        relativeLower 9 3 SparseWilsonCurvature.witnessAngle := by
  refine ⟨?_, ?_, rational_slack_three⟩
  · have hp := Real.pi_gt_three
    norm_num [SparseWilsonCurvature.witnessAngle]
    linarith
  · intro p hp
    exact rational_strict_log_cap p hp

end OperatorDerivativeRewrite.Foundation.SparseBlockGoodRegionObstruction
