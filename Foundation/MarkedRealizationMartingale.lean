import Foundation.MarkedRealizationIndependence
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Martingale.Basic

/-! Actual bounded-mark renewal processes give native compensated natural-filtration martingales. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedRealizationMartingale
open MarkedRenewalRealization MarkedRealizationRegeneration MarkedRealizationPast
variable {A : Type*} [MeasurableSpace A]

def value (z : A → ℂ) (t : ℝ≥0) : Sample A → ℂ := process z t

def history (z : A → ℂ) (hz : Measurable z) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Sample A)) :=
  Filtration.natural (value z) (fun t => (process_measurable z hz t).stronglyMeasurable)

theorem value_adapted (z : A → ℂ) (hz : Measurable z) :
    StronglyAdapted (history z hz) (value z) :=
  Filtration.stronglyAdapted_natural (u := value z)
    (fun t : ℝ≥0 => (process_measurable z hz t).stronglyMeasurable)

theorem difference_eq_future (z : A → ℂ) (s t : ℝ≥0) (hst : s ≤ t) (ω : Sample A) :
    value z t ω-value z s ω = futurePath z s ω (t-s) := by
  have he : (s : ℝ)+((t-s : ℝ≥0) : ℝ) = (t : ℝ) := by rw [NNReal.coe_sub hst]; ring
  simp only [value,futurePath,he]

theorem difference_independent_past (μ : Measure A) [IsProbabilityMeasure μ]
    (z : A → ℂ) (hz : Measurable z) (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => value z t ω-value z s ω) inferInstance)
      (history z hz s) (probability μ) := by
  have hi := (MarkedRealizationIndependence.past_future_independent μ z hz s).symm.comp
    (measurable_pi_apply (t-s)) measurable_id
  have he : (fun ω => value z t ω-value z s ω) =
      (fun γ : ProcessPath => γ (t-s)) ∘ futurePath z s := funext (difference_eq_future z s t hst)
  have hh : history z hz s = MeasurableSpace.comap (pastPath z s) inferInstance :=
    Filtration.natural_eq_comap (value z)
      (fun t => (process_measurable z hz t).stronglyMeasurable) s
  rw [he,hh]
  exact hi

theorem value_integrable (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (t : ℝ≥0) :
    Integrable (value z t) (probability μ) := process_integrable μ z hz C hC t

theorem difference_mean (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (s t : ℝ≥0) :
    (∫ ω, value z t ω-value z s ω ∂probability μ) =
      ((t : ℂ)-(s : ℂ))*(∫ x, z x ∂μ) := by
  rw [integral_sub (value_integrable μ z hz C hC t) (value_integrable μ z hz C hC s)]
  change (∫ ω, process z t ω ∂probability μ)-(∫ ω, process z s ω ∂probability μ) = _
  rw [process_mean μ z hz C hC t,process_mean μ z hz C hC s]
  ring

theorem difference_condExp (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (s t : ℝ≥0) (hst : s ≤ t) :
    (probability μ)[fun ω => value z t ω-value z s ω | history z hz s] =ᵐ[probability μ]
      fun _ => ((t : ℂ)-(s : ℂ))*(∫ x, z x ∂μ) := by
  have hm := (process_measurable z hz t).sub (process_measurable z hz s)
  have he := condExp_indep_eq hm.comap_le ((history z hz).le s)
    (comap_measurable (fun ω => value z t ω-value z s ω)).stronglyMeasurable
    (difference_independent_past μ z hz s t hst)
  simpa only [difference_mean μ z hz C hC s t] using he

theorem value_condExp (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (s t : ℝ≥0) (hst : s ≤ t) :
    (probability μ)[value z t | history z hz s] =ᵐ[probability μ]
      fun ω => value z s ω+((t : ℂ)-(s : ℂ))*(∫ x, z x ∂μ) := by
  have he := condExp_sub (value_integrable μ z hz C hC t)
    (value_integrable μ z hz C hC s) (history z hz s)
  have hp := condExp_of_stronglyMeasurable (μ := probability μ) ((history z hz).le s)
    (value_adapted z hz s) (value_integrable μ z hz C hC s)
  rw [hp] at he
  have hd := difference_condExp μ z hz C hC s t hst
  filter_upwards [he,hd] with ω he hd
  change (probability μ)[value z t-value z s | history z hz s] ω =
    (probability μ)[value z t | history z hz s] ω-value z s ω at he
  change (probability μ)[value z t-value z s | history z hz s] ω = _ at hd
  have heq := he.symm.trans hd
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp heq)

def centered (μ : Measure A) (z : A → ℂ) (t : ℝ≥0) (ω : Sample A) : ℂ :=
  value z t ω-(t : ℂ)*(∫ x, z x ∂μ)

theorem centered_integrable (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (t : ℝ≥0) :
    Integrable (centered μ z t) (probability μ) :=
  (value_integrable μ z hz C hC t).sub (integrable_const _)

theorem centered_adapted (μ : Measure A) (z : A → ℂ) (hz : Measurable z) :
    StronglyAdapted (history z hz) (centered μ z) := fun t =>
  (value_adapted z hz t).sub stronglyMeasurable_const

theorem centered_martingale (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) :
    Martingale (centered μ z) (history z hz) (probability μ) := by
  refine ⟨centered_adapted μ z hz,?_⟩
  intro s t hst
  have he := condExp_sub (value_integrable μ z hz C hC t)
    (integrable_const ((t : ℂ)*(∫ x, z x ∂μ))) (history z hz s)
  rw [condExp_const ((history z hz).le s)] at he
  have hp := value_condExp μ z hz C hC s t hst
  filter_upwards [he,hp] with ω he hp
  change (probability μ)[centered μ z t | history z hz s] ω = centered μ z s ω
  change (probability μ)[centered μ z t | history z hz s] ω = _ at he
  rw [he]
  change (probability μ)[value z t | history z hz s] ω-
    (t : ℂ)*(∫ x, z x ∂μ) = centered μ z s ω
  rw [hp]
  unfold centered
  ring

theorem value_martingale (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (hmean : (∫ x, z x ∂μ) = 0) :
    Martingale (value z) (history z hz) (probability μ) := by
  refine ⟨value_adapted z hz,?_⟩
  intro s t hst
  simpa only [hmean,mul_zero,add_zero] using value_condExp μ z hz C hC s t hst

end OperatorDerivativeRewrite.Foundation.MarkedRealizationMartingale
