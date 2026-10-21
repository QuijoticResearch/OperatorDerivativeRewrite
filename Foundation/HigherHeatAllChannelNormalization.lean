import Foundation.HigherHeatAllPowerBounds
import Foundation.HigherHeatFourthChannelSteps

/-! Factorial normalization of every signed Itô channel, including the drift. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAllChannelNormalization
open HigherHeatAllProductChannels HigherHeatAllPowerBounds HigherHeatPairedDualCausality
open HigherHeatWeakTimeAdjoint HigherHeatSecondChannelSteps HigherHeatThirdChannelSteps
open HigherHeatFourthChannelSteps

/-- Index r represents the stochastic increment power r+1. -/
def channel (m : ℕ) (T : ℝ≥0) (r : ℕ) : Field timeMeasure →L[ℝ] Dual :=
  r.factorial • productChannel m T r

theorem channel_eq (m : ℕ) (T : ℝ≥0) (r : ℕ) :
    channel m T r =
      (coefficient m T * ((2*m-1).descFactorial r:ℝ)) • transpose timeMeasure (2*m-1-r) := by
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro G
  simp only [channel, productChannel, smul_apply, nsmul_eq_mul, smul_eq_mul,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  ring

theorem channel_bound (m : ℕ) (T : ℝ≥0) (r : ℕ) (A : Field timeMeasure) :
    ‖channel m T r A‖ ≤ ((2*m:ℕ):ℝ)*(T:ℝ)*((2*m-1).descFactorial r:ℝ)*‖A‖ := by
  have h := (norm_nsmul_le (a := productChannel m T r A) (n := r.factorial)).trans
    (mul_le_mul_of_nonneg_left (productChannel_bound m T r A) (Nat.cast_nonneg r.factorial))
  change ‖r.factorial • productChannel m T r A‖ ≤ _
  exact h.trans_eq (by simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]; ring)

theorem first_channel (m : ℕ) (T : ℝ≥0) : channel m T 0 = firstChannel m T := by
  simpa only [channel, Nat.factorial_zero, one_nsmul] using
    HigherHeatAllProductChannels.first_channel m T

theorem second_channel (m : ℕ) (T : ℝ≥0) : channel m T 1 = secondChannel m T := by
  simp [channel, productChannel, secondChannel, Nat.sub_sub]

theorem third_biharmonic (T : ℝ≥0) : channel 2 T 2 = thirdChannel T := by
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro G
  simp only [channel_eq, thirdChannel, smul_apply, smul_eq_mul]
  have hc : ((2*2-1).descFactorial 2:ℝ) = 6 := by norm_num
  rw [hc]
  change (coefficient 2 T * 6) * transpose timeMeasure 1 A G =
    (6*coefficient 2 T) * transpose timeMeasure 1 A G
  ring

theorem fourth_biharmonic (T : ℝ≥0) : channel 2 T 3 = fourthChannel T := by
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro G
  simp only [channel_eq, fourthChannel, smul_apply, smul_eq_mul]
  have hc : ((2*2-1).descFactorial 3:ℝ) = 6 := by norm_num
  rw [hc]
  change (coefficient 2 T * 6) * transpose timeMeasure 0 A G =
    (6*coefficient 2 T) * transpose timeMeasure 0 A G
  ring

theorem drift_normalization (m : ℕ) (hm : 0 < m) (T : ℝ≥0) :
    channel m T (2*m-1) =
      (((2*m).factorial:ℝ)*(-1:ℝ)^(m+1)*(T:ℝ)) • transpose timeMeasure 0 := by
  rw [channel_eq, Nat.descFactorial_self, Nat.sub_self]
  have he : 2*m-1+1=2*m := by omega
  have hf := Nat.factorial_succ (2*m-1)
  rw [he] at hf
  congr 1
  rw [hf, Nat.cast_mul]
  unfold coefficient
  ring

theorem channel_zero_above_order (m : ℕ) (T : ℝ≥0) (r : ℕ) (hr : 2*m ≤ r) :
    channel m T r = 0 := by
  rw [channel_eq]
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro G
  change (coefficient m T * ((2*m-1).descFactorial r:ℝ)) *
    transpose timeMeasure (2*m-1-r) A G = 0
  by_cases hm : m=0
  · subst m
    simp [coefficient]
  · rw [Nat.descFactorial_of_lt (by omega : 2*m-1 < r)]
    simp

end OperatorDerivativeRewrite.Foundation.HigherHeatAllChannelNormalization
