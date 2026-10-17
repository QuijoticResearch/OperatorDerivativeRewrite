import Foundation.ExponentialHoldingSequence
import Mathlib.Probability.StrongLaw

/-! Actual exponential arrival clocks are strictly increasing and nonexplosive almost surely. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ExponentialNonexplosiveClock
open ExponentialHoldingSequence

def clock (n : ℕ) (ω : Sample) : ℝ := ∑ i ∈ Finset.range n, holding i ω

theorem clock_measurable (n : ℕ) : Measurable (clock n) :=
  Finset.measurable_sum _ (fun i _ => holding_measurable i)

theorem clock_zero (ω : Sample) : clock 0 ω = 0 := by simp [clock]

theorem clock_successor (n : ℕ) (ω : Sample) : clock (n+1) ω = clock n ω+holding n ω := by
  simp only [clock, Finset.sum_range_succ]

theorem success_le_holding (n : ℕ) (ω : Sample) (h : 0 ≤ holding n ω) :
    success n ω ≤ holding n ω := by
  by_cases hx : 1 < holding n ω
  · rw [success, successMap, indicator_of_mem (show holding n ω ∈ Ioi 1 from hx)]
    exact hx.le
  · rw [success, successMap, indicator_of_notMem (show holding n ω ∉ Ioi 1 from hx)]
    exact h

theorem success_strong_law : ∀ᵐ ω ∂probability,
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, success i ω)/(n : ℝ))
      atTop (𝓝 (Real.exp (-1))) := by
  have he := strong_law_ae_real success (success_integrable 0)
    (fun i j hij => success_independent.indepFun hij) (fun i => success_identDistrib i 0)
  simpa only [success_integral] using he

theorem clock_tendsto : ∀ᵐ ω ∂probability, Tendsto (fun n => clock n ω) atTop atTop := by
  filter_upwards [holding_positive, success_strong_law] with ω hpos hlim
  have hp : 0 < Real.exp (-1)/2 := by positivity
  have he : ∀ᶠ n : ℕ in atTop,
      Real.exp (-1)/2 < (∑ i ∈ Finset.range n, success i ω)/(n : ℝ) :=
    hlim.eventually (Ioi_mem_nhds (by have h := Real.exp_pos (-1); linarith))
  have hb : ∀ᶠ n : ℕ in atTop, (Real.exp (-1)/2)*(n : ℝ) ≤ clock n ω := by
    filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
    have hs := (lt_div_iff₀ hnr).mp hn
    have hc : (∑ i ∈ Finset.range n, success i ω) ≤ clock n ω :=
      Finset.sum_le_sum (fun i _ => success_le_holding i ω (hpos i).le)
    exact hs.le.trans hc
  have hl : Tendsto (fun n : ℕ => (Real.exp (-1)/2)*(n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop hp
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hb, hl.eventually (eventually_ge_atTop b)] with n hn hbn
  exact hbn.trans hn

def Good (ω : Sample) : Prop :=
  (∀ n, 0 < holding n ω) ∧ ∀ k : ℕ, ∃ n : ℕ, (k : ℝ) < clock n ω

theorem good_measurable : MeasurableSet {ω : Sample | Good ω} := by
  change MeasurableSet ({ω : Sample | ∀ n, 0 < holding n ω} ∩
    {ω : Sample | ∀ k : ℕ, ∃ n : ℕ, (k : ℝ) < clock n ω})
  apply MeasurableSet.inter
  · simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro n
    exact measurableSet_lt measurable_const (holding_measurable n)
  · simp only [setOf_forall, setOf_exists]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iUnion
    intro n
    exact measurableSet_lt measurable_const (clock_measurable n)

theorem good_ae : ∀ᵐ ω ∂probability, Good ω := by
  filter_upwards [holding_positive, clock_tendsto] with ω hp ht
  exact ⟨hp, fun k => (ht.eventually (eventually_gt_atTop (k : ℝ))).exists⟩

theorem good_strictMono {ω : Sample} (h : Good ω) : StrictMono (fun n => clock n ω) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [clock_successor]
  linarith [h.1 n]

theorem good_exists_above {ω : Sample} (h : Good ω) (t : ℝ) : ∃ n, t < clock n ω := by
  obtain ⟨k,hk⟩ := exists_nat_gt t
  obtain ⟨n,hn⟩ := h.2 k
  exact ⟨n,hk.trans hn⟩

end OperatorDerivativeRewrite.Foundation.ExponentialNonexplosiveClock
