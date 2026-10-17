import Foundation.RenewalPastFutureIndependence
import Foundation.SequentialIncrementIndependence

/-! Native natural-filtration independent increments for the actual exponential renewal process. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.RenewalIndependentIncrements
open ExponentialHoldingSequence ExponentialRenewalCount ExponentialSourceRegeneration
open RenewalConditionalFuturePath RenewalPastReconstruction

def process (t : ℝ≥0) (ω : Sample) : ℝ := count t ω

theorem process_measurable (t : ℝ≥0) : Measurable (process t) :=
  (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (count_measurable t)

def history : Filtration ℝ≥0 (inferInstance : MeasurableSpace Sample) :=
  Filtration.natural (fun t : ℝ≥0 => count t) (fun t => (count_measurable t).stronglyMeasurable)

theorem count_adapted : StronglyAdapted history (fun t : ℝ≥0 => count t) :=
  Filtration.stronglyAdapted_natural (u := fun t : ℝ≥0 => count t)
    (fun t : ℝ≥0 => (count_measurable t).stronglyMeasurable)

theorem process_adapted (t : ℝ≥0) : Measurable[history t] (process t) :=
  (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (count_adapted t).measurable

theorem difference_eq_future (s t : ℝ≥0) (hst : s ≤ t) (ω : Sample) :
    process t ω-process s ω = ((futurePath s ω) (t-s) : ℝ) := by
  have hsum : (s : ℝ)+((t-s : ℝ≥0) : ℝ) = (t : ℝ) := by rw [NNReal.coe_sub hst]; ring
  simp only [process, futurePath, hsum]
  rw [Nat.cast_sub (count_monotone ω (show (s : ℝ) ≤ t from hst))]

theorem difference_independent_past (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => process t ω-process s ω) inferInstance)
      (history s) probability := by
  let ev : CountPath → ℝ := fun γ => (γ (t-s) : ℝ)
  have hm : Measurable ev := (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    (measurable_pi_apply (t-s))
  have hi := (RenewalPastFutureIndependence.past_future_independent s).symm.comp hm measurable_id
  have he : (fun ω => process t ω-process s ω) = ev ∘ futurePath s :=
    funext (difference_eq_future s t hst)
  rw [he, history, Filtration.natural_eq_comap]
  exact hi

theorem hasIndepIncrements : HasIndepIncrements process probability :=
  SequentialIncrementIndependence.of_filtration probability history process process_adapted
    difference_independent_past

theorem process_zero (ω : Sample) : process 0 ω = 0 := by simp [process, count_zero]

theorem realPath_cadlag (ω : Sample) : IsCadlag (fun t : ℝ => (count t ω : ℝ)) := by
  have he := (ExponentialRenewalCadlag.count_cadlag ω).continuous_comp
    (show Continuous (fun k : ℕ => (k : ℝ)) from continuous_of_discreteTopology)
  simpa only [Function.comp_def] using he

end OperatorDerivativeRewrite.Foundation.RenewalIndependentIncrements
