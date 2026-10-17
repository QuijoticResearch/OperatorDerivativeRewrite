import Foundation.ExponentialRenewalCount
import Mathlib.Topology.Order.Cadlag

/-! Native cadlag paths of the actually constructed finite exponential renewal count. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ExponentialRenewalCadlag
open ExponentialHoldingSequence ExponentialNonexplosiveClock ExponentialRenewalCount

theorem count_nonpos (ω : Sample) (t : ℝ) (ht : t ≤ 0) : count t ω = 0 :=
  Nat.le_zero.mp ((count_monotone ω ht).trans_eq (count_zero ω))

theorem right_constant {ω : Sample} (h : Good ω) (t : ℝ) :
    (fun u => count u ω) =ᶠ[𝓝[>] t] (fun _ => count t ω) := by
  have he : ∀ᶠ u : ℝ in 𝓝[>] t, u < clock (firstAbove t ω) ω :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds (firstAbove_above h t))
  filter_upwards [he, self_mem_nhdsWithin] with u hu hut
  apply Nat.le_antisymm
  · apply Nat.sub_le_sub_right
    exact firstAbove_le h u _ hu
  · exact count_monotone ω (le_of_lt hut)

theorem count_rightContinuous (ω : Sample) : IsRightContinuous (fun t : ℝ => count t ω) := by
  by_cases h : Good ω
  · intro t
    exact tendsto_const_nhds.congr' (right_constant h t).symm
  · have he : Continuous (fun t : ℝ => count t ω) := by
      simpa only [count_bad h] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℕ)))
    exact he.isRightContinuous

theorem count_cadlag (ω : Sample) : IsCadlag (fun t : ℝ => count t ω) := by
  refine ⟨count_rightContinuous ω, ?_⟩
  intro t
  exact ⟨_, (count_monotone ω).tendsto_nhdsLT t⟩

end OperatorDerivativeRewrite.Foundation.ExponentialRenewalCadlag
