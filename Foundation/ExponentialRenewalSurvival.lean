import Foundation.RootRenewalOperatorBridge

/-! Actual renewal count events reduce to actual arrival events; first survival is exponential. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace OperatorDerivativeRewrite.Foundation.ExponentialRenewalSurvival
open ExponentialHoldingSequence ExponentialNonexplosiveClock ExponentialRenewalCount

theorem count_le_iff {ω : Sample} (h : Good ω) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    count t ω ≤ n ↔ t < clock (n+1) ω := by
  constructor
  · intro hn
    exact lt_of_lt_of_le (count_interval h t ht).2
      ((good_strictMono h).monotone (Nat.add_le_add_right hn 1))
  · intro hn
    have he := firstAbove_le h t (n+1) hn
    rw [← count_successor h t ht] at he
    omega

theorem count_zero_iff {ω : Sample} (h : Good ω) (t : ℝ) (ht : 0 ≤ t) :
    count t ω = 0 ↔ t < holding 0 ω := by
  have he := count_le_iff h t ht 0
  simpa only [Nat.le_zero, zero_add, clock_successor, clock_zero] using he

theorem count_cdf_arrival (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (RootRenewalOperatorBridge.countLaw t) (Iic n) =
      (probability.map (clock (n+1))) (Ioi t) := by
  rw [RootRenewalOperatorBridge.countLaw,
    Measure.map_apply (count_measurable t) measurableSet_Iic,
    Measure.map_apply (clock_measurable (n+1)) measurableSet_Ioi]
  apply measure_congr
  filter_upwards [good_ae] with ω h
  exact propext (count_le_iff h t ht n)

theorem base_survival (t : ℝ) (ht : 0 ≤ t) : base.real (Ioi t) = Real.exp (-t) := by
  have he := measureReal_compl (μ := base) (s := Iic t) measurableSet_Iic
  rw [compl_Iic, probReal_univ, base_cdf, ite_eq_left ht] at he
  linarith

theorem first_survival (t : ℝ) (ht : 0 ≤ t) :
    (RootRenewalOperatorBridge.countLaw t).real {0} = Real.exp (-t) := by
  have he := count_cdf_arrival t ht 0
  have hc : clock (0+1) = holding 0 := by
    funext ω
    simp only [clock_successor, clock_zero, zero_add]
  rw [hc, holding_law] at he
  have hs : Iic (0 : ℕ) = {0} := by ext n; simp
  rw [hs] at he
  exact (congrArg ENNReal.toReal he).trans (base_survival t ht)

end OperatorDerivativeRewrite.Foundation.ExponentialRenewalSurvival
