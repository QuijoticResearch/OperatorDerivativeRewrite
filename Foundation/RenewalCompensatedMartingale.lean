import Foundation.RenewalIndependentIncrements
import Foundation.PoissonCountMoments
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation

/-! A native continuous-time compensated martingale on the actual renewal source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.RenewalCompensatedMartingale
open ExponentialHoldingSequence ExponentialRenewalCount RenewalIndependentIncrements

theorem count_preserving (t : ℝ≥0) : MeasurePreserving (count t) probability (poissonMeasure t) :=
  ⟨count_measurable t,ConstructedRenewalPoissonLaw.countLaw_eq_poisson t⟩

theorem process_integrable (t : ℝ≥0) : Integrable (process t) probability := by
  have hm : Measurable (fun k : ℕ => (k : ℝ)) := measurable_of_countable _
  have hi : Integrable (fun k : ℕ => (k : ℝ)) (probability.map (count t)) := by
    rw [(count_preserving t).map_eq]
    exact PoissonCountMoments.count_integrable t
  exact (integrable_map_measure hm.aestronglyMeasurable (count_measurable t).aemeasurable).mp hi

theorem process_mean (t : ℝ≥0) : (∫ ω, process t ω ∂probability) = (t : ℝ) := by
  have hm : Measurable (fun k : ℕ => (k : ℝ)) := measurable_of_countable _
  have he := integral_map (μ := probability) (count_measurable t).aemeasurable
    hm.aestronglyMeasurable
  rw [(count_preserving t).map_eq, PoissonCountMoments.count_integral] at he
  exact he.symm

theorem difference_mean (s t : ℝ≥0) :
    (∫ ω, process t ω-process s ω ∂probability) = (t : ℝ)-(s : ℝ) := by
  rw [integral_sub (process_integrable t) (process_integrable s), process_mean, process_mean]

theorem difference_condExp (s t : ℝ≥0) (hst : s ≤ t) :
    probability[fun ω => process t ω-process s ω | history s] =ᵐ[probability]
      fun _ => (t : ℝ)-(s : ℝ) := by
  have hm := (process_measurable t).sub (process_measurable s)
  have he := condExp_indep_eq hm.comap_le (history.le s)
    (comap_measurable (fun ω => process t ω-process s ω)).stronglyMeasurable
    (difference_independent_past s t hst)
  simpa only [difference_mean] using he

theorem process_condExp (s t : ℝ≥0) (hst : s ≤ t) :
    probability[process t | history s] =ᵐ[probability]
      fun ω => process s ω + (t : ℝ)-(s : ℝ) := by
  have he := condExp_sub (process_integrable t) (process_integrable s) (history s)
  have hp := condExp_of_stronglyMeasurable (μ := probability) (history.le s)
    (process_adapted s).stronglyMeasurable (process_integrable s)
  have hd := difference_condExp s t hst
  rw [hp] at he
  filter_upwards [he,hd] with ω he hd
  change probability[process t-process s | history s] ω =
    probability[process t | history s] ω-process s ω at he
  change probability[process t-process s | history s] ω = (t : ℝ)-(s : ℝ) at hd
  linarith

def compensated (t : ℝ≥0) (ω : Sample) : ℝ := process t ω-t

theorem compensated_integrable (t : ℝ≥0) : Integrable (compensated t) probability :=
  (process_integrable t).sub (integrable_const (t : ℝ))

theorem compensated_adapted : StronglyAdapted history compensated := fun t =>
  ((process_adapted t).sub measurable_const).stronglyMeasurable

theorem compensated_martingale : Martingale compensated history probability := by
  refine ⟨compensated_adapted, ?_⟩
  intro s t hst
  have he := condExp_sub (process_integrable t) (integrable_const (t : ℝ)) (history s)
  rw [condExp_const (history.le s)] at he
  have hp := process_condExp s t hst
  have hc : probability[compensated t | history s] =ᵐ[probability]
      fun ω => probability[process t | history s] ω-(t : ℝ) := by
    have hfun : compensated t = process t-(fun _ : Sample => (t : ℝ)) := rfl
    rw [hfun]
    exact he
  filter_upwards [hc,hp] with ω hc hp
  change probability[compensated t | history s] ω = process s ω-(s : ℝ)
  rw [hc,hp]
  ring

end OperatorDerivativeRewrite.Foundation.RenewalCompensatedMartingale
