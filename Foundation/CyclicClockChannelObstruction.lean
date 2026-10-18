import Foundation.CyclicCenteredKernel
import Foundation.RenewalCompensatedMartingale

/-! Centered mark channels omit the separate compensated-count clock channel. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CyclicClockChannelObstruction
open ExponentialNonexplosiveClock ExponentialRenewalCount
variable (N : ℕ) [NeZero N]

theorem constant_kernel_forces_zero (u : ZMod N → ℂ) (c : ℂ)
    (h : ∀ k, CyclicCenteredKernel.kernel N u k = c) : c = 0 := by
  have he := integral_congr_ae (μ := CyclicRootProbabilityNoise.probability N)
    (Filter.Eventually.of_forall h)
  rw [CyclicCenteredKernel.kernel_mean,integral_const,probReal_univ,one_smul] at he
  exact he.symm

theorem unit_gain_not_representable :
    ¬ ∃ u : ZMod N → ℂ, ∀ k, CyclicCenteredKernel.kernel N u k = 1 := by
  rintro ⟨u,hu⟩
  exact one_ne_zero (constant_kernel_forces_zero N u 1 hu)

theorem count_jump_not_representable (ω : ExponentialHoldingSequence.Sample) (hω : Good ω) (n : ℕ) :
    ¬ ∃ u : ZMod N → ℂ, ∀ k, CyclicCenteredKernel.kernel N u k =
      (count (clock (n+1) ω) ω : ℂ)-(count (clock n ω) ω : ℂ) := by
  have he : (count (clock (n+1) ω) ω : ℂ)-(count (clock n ω) ω : ℂ) = 1 := by
    rw [count_at_clock hω (n+1),count_at_clock hω n]
    push_cast
    ring
  simpa only [he] using unit_gain_not_representable N

end OperatorDerivativeRewrite.Foundation.CyclicClockChannelObstruction
