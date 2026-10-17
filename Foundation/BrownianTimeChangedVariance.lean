import Foundation.BrownianTimeChangedMartingales
import Foundation.BrownianAugmentedSquare
import Foundation.BrownianStickyNontriviality

/-! The actual sticky-candidate martingale has variance equal to expected
inverse time, strictly below physical time when holding is nontrivial. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianTimeChangedVariance
open InfiniteGaussian IBMConstructedSources BrownianMassRandomTimeChange
open BrownianMassClockStoppingTime BrownianTimeChangedMartingales
open ContinuousTimeChangeMartingale
set_option backward.isDefEq.respectTransparency false

theorem inverse_integrable (κ t : ℝ≥0) :
    Integrable (fun ω => (inverse κ ω t : ℝ)) gaussianProduct := by
  apply (integrable_const (t : ℝ)).mono'
    ((NNReal.continuous_coe.measurable.comp (inverse_coordinate_measurable κ t)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun ω => by
    change ‖(inverse κ ω t : ℝ)‖ ≤ (t : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (inverse κ ω t).coe_nonneg]
    exact_mod_cast inverse_le κ ω t)

theorem changed_square_martingale (κ : ℝ≥0) :
    Martingale (fun t ω => (changedPath κ ω t)^2-(inverse κ ω t : ℝ))
      (physicalPast κ) gaussianProduct :=
  changed_martingale gaussianProduct augmentedPast BrownianAugmentedSquare.value
    (fun t ω => inverse κ ω t) (inverse_isStoppingTime κ) (fun ω => inverse_monotone κ ω)
    BrownianAugmentedSquare.value_martingale BrownianAugmentedSquare.value_continuous
    (fun t ω => inverse_le κ ω t)

theorem changed_square_integrable (κ t : ℝ≥0) :
    Integrable (fun ω => (changedPath κ ω t)^2) gaussianProduct := by
  have h := ((changed_square_martingale κ).integrable t).add (inverse_integrable κ t)
  have he : ((fun ω => (changedPath κ ω t)^2-(inverse κ ω t : ℝ))+
      (fun ω => (inverse κ ω t : ℝ))) = fun ω => (changedPath κ ω t)^2 := by
    funext ω
    simp
  rw [he] at h
  exact h

theorem stopped_square_centered (κ t : ℝ≥0) :
    (∫ ω, (changedPath κ ω t)^2-(inverse κ ω t : ℝ) ∂gaussianProduct) = 0 := by
  have h := ContinuousBoundedSampling.stopped_expectation gaussianProduct augmentedPast
    BrownianAugmentedSquare.value BrownianAugmentedSquare.value_martingale
    BrownianAugmentedSquare.value_continuous (fun ω => inverse κ ω t)
    (inverse_isStoppingTime κ t) (Nat.ceil t)
    (fun ω => (inverse_le κ ω t).trans (Nat.le_ceil t))
  exact h.trans (BrownianAugmentedSquare.value_centered _)

theorem changed_second_moment (κ t : ℝ≥0) :
    (∫ ω, (changedPath κ ω t)^2 ∂gaussianProduct) =
      ∫ ω, (inverse κ ω t : ℝ) ∂gaussianProduct := by
  have h := stopped_square_centered κ t
  rw [integral_sub (changed_square_integrable κ t) (inverse_integrable κ t)] at h
  linarith

theorem holding_variance_balance (κ t : ℝ≥0) :
    (∫ ω, (changedPath κ ω t)^2 ∂gaussianProduct)+
      (∫ ω, BrownianStickyNontriviality.occupation κ ω t ∂gaussianProduct) = (t : ℝ) := by
  rw [changed_second_moment]
  have he : (fun ω => BrownianStickyNontriviality.occupation κ ω t) =ᵐ[gaussianProduct]
      (fun ω => (t : ℝ)-(inverse κ ω t : ℝ)) :=
    BrownianStickyNontriviality.occupation_gap.mono (fun ω hω => hω κ t)
  rw [integral_congr_ae he, integral_sub (integrable_const (t : ℝ)) (inverse_integrable κ t)]
  simp

theorem changed_second_moment_lt_time (κ t : ℝ≥0) (hκ : 0 < κ) (ht : 0 < t) :
    (∫ ω, (changedPath κ ω t)^2 ∂gaussianProduct) < (t : ℝ) := by
  have h := holding_variance_balance κ t
  have hp := BrownianStickyNontriviality.expected_occupation_pos κ t hκ ht
  linarith

end OperatorDerivativeRewrite.Foundation.BrownianTimeChangedVariance
