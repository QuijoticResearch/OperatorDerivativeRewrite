import Foundation.ComplexRootChannelOperator
import Foundation.MarkedJumpIto

/-! Actual jump sums split into a clock channel and three centered mark channels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.MarkedChannelIto
open MarkedRootRenewalProcess (StateSample probability position)
open MarkedRenewalMartingale MarkedTimeIntegral
open ComplexRootTransitionOperator (Test)
open ComplexRootChannelOperator

def channelSum (a : ℝ) (r : Fin 3) (f : Test) (t : ℝ≥0) (ω : StateSample) : ℂ :=
  ∑ j ∈ Finset.range (ExponentialRenewalCount.count t ω.1),
    channel a r f (position a j ω.2) * (ComplexFourthRootNoise.noise a (ω.2 j))^(r.val+1)

def clockSum (a : ℝ) (f : Test) (t : ℝ≥0) (ω : StateSample) : ℂ :=
  ∑ j ∈ Finset.range (ExponentialRenewalCount.count t ω.1),
    ComplexRootTransitionOperator.generator 1 a f (position a j ω.2)

def compensatedClock (a : ℝ) (f : Test) (t : ℝ≥0) (ω : StateSample) : ℂ :=
  clockSum a f t ω - primitive a (ComplexRootTransitionOperator.generator 1 a f) t ω

theorem jump_channels (a : ℝ) (ha : a ≠ 0) (f : Test) (t : ℝ≥0) (ω : StateSample) :
    MarkedJumpIto.jumpSum a f t ω = clockSum a f t ω + channelSum a 0 f t ω +
      channelSum a 1 f t ω + channelSum a 2 f t ω := by
  unfold MarkedJumpIto.jumpSum clockSum channelSum
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_add, pow_one] using
    jump_kernel_decomposition a ha f (position a j ω.2) (ω.2 j)

theorem channelSum_leftLim (a : ℝ) (r : Fin 3) (f : Test) (t : ℝ≥0) (ω : StateSample)
    (hω : ExponentialNonexplosiveClock.Good ω.1) :
    channelSum a r f t ω = ∑ j ∈ Finset.range (ExponentialRenewalCount.count t ω.1),
      (channel a r f (Function.leftLim (fun u : ℝ => MarkedRootRenewalProcess.process a u ω)
        (ExponentialNonexplosiveClock.clock (j+1) ω.1)) *
      (MarkedRootRenewalProcess.process a (ExponentialNonexplosiveClock.clock (j+1) ω.1) ω -
        Function.leftLim (fun u : ℝ => MarkedRootRenewalProcess.process a u ω)
          (ExponentialNonexplosiveClock.clock (j+1) ω.1))^(r.val+1)) := by
  unfold channelSum
  apply Finset.sum_congr rfl
  intro j _
  rw [MarkedJumpIto.actual_jump a ω hω j, MarkedJumpIto.process_leftLim a ω hω j]

theorem compensated_representation (a : ℝ) (ha : a ≠ 0) (f : Test) :
    (fun t ω => compensatedClock a f t ω + channelSum a 0 f t ω +
      channelSum a 1 f t ω + channelSum a 2 f t ω) = MarkedJumpIto.compensated a f := by
  funext t ω
  have he := jump_channels a ha f t ω
  unfold compensatedClock MarkedJumpIto.compensated
  linear_combination -he

theorem combined_martingale (a : ℝ) (ha : a ≠ 0) (f : Test) :
    Martingale (fun t ω => compensatedClock a f t ω + channelSum a 0 f t ω +
      channelSum a 1 f t ω + channelSum a 2 f t ω) (history a) probability := by
  rw [compensated_representation a ha f]
  exact MarkedJumpIto.compensated_martingale a f

end OperatorDerivativeRewrite.Foundation.MarkedChannelIto
