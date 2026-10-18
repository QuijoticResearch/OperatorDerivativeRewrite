import Foundation.MarkedRealizationMartingale
import Foundation.IndependentInnovationConditioning

/-! Genuine transition operators are native conditional expectations of the constructed process. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedRealizationMarkov
open MarkedRenewalRealization MarkedRealizationRegeneration MarkedRealizationPast
open MarkedRealizationMartingale
variable {A : Type*} [MeasurableSpace A]

theorem history_eq_past (z : A → ℂ) (hz : Measurable z) (s : ℝ≥0) :
    history z hz s = MeasurableSpace.comap (pastPath z s) inferInstance :=
  Filtration.natural_eq_comap (value z) (fun t => (process_measurable z hz t).stronglyMeasurable) s

theorem past_increment_independent (μ : Measure A) [IsProbabilityMeasure μ]
    (z : A → ℂ) (hz : Measurable z) (s t : ℝ≥0) (hst : s ≤ t) :
    IndepFun (pastPath z s) (fun ω => value z t ω-value z s ω) (probability μ) := by
  change Indep (MeasurableSpace.comap (pastPath z s) inferInstance)
    (MeasurableSpace.comap (fun ω => value z t ω-value z s ω) inferInstance) (probability μ)
  rw [← history_eq_past z hz s]
  exact (difference_independent_past μ z hz s t hst).symm

theorem increment_law (μ : Measure A) [IsProbabilityMeasure μ]
    (z : A → ℂ) (hz : Measurable z) (s t : ℝ≥0) (hst : s ≤ t) :
    (probability μ).map (fun ω => value z t ω-value z s ω) =
      (probability μ).map (value z (t-s)) := by
  have he := congrArg (fun ν : Measure ProcessPath => ν.map (fun γ => γ (t-s)))
    (MarkedRealizationIndependence.future_law μ z hz s)
  rw [Measure.map_map (measurable_pi_apply (t-s)) (futurePath_measurable z hz s),
    Measure.map_map (measurable_pi_apply (t-s)) (path_measurable z hz)] at he
  have hf : (fun ω => value z t ω-value z s ω) =
      (fun γ : ProcessPath => γ (t-s)) ∘ futurePath z s := funext (difference_eq_future z s t hst)
  rw [hf]
  exact he

def transition (μ : Measure A) (z : A → ℂ) (t : ℝ≥0) (F : ℂ → ℂ) (x : ℂ) : ℂ :=
  ∫ ω, F (x+value z t ω) ∂probability μ

theorem conditional_transition (μ : Measure A) [IsProbabilityMeasure μ]
    (z : A → ℂ) (hz : Measurable z) (s t : ℝ≥0) (hst : s ≤ t)
    (F : ℂ → ℂ) (hF : Measurable F) (hI : Integrable (fun ω => F (value z t ω)) (probability μ)) :
    (probability μ)[fun ω => F (value z t ω) | history z hz s] =ᵐ[probability μ]
      fun ω => transition μ z (t-s) F (value z s ω) := by
  let G : PastPath s × ℂ → ℂ := fun p => F (p.1 ⟨s,by simp⟩+p.2)
  have hG : Measurable G := hF.comp
    (((measurable_pi_apply (⟨s,by simp⟩ : Set.Iic s)).comp measurable_fst).add measurable_snd)
  have hfun : (fun ω => G (pastPath z s ω,value z t ω-value z s ω)) =
      (fun ω => F (value z t ω)) := by
    funext ω
    change F (value z s ω+(value z t ω-value z s ω)) = _
    congr 1
    abel
  have hi : Integrable (fun ω => G (pastPath z s ω,value z t ω-value z s ω)) (probability μ) :=
    hfun.symm ▸ hI
  have he := IndependentInnovationConditioning.conditional_integral (probability μ)
    (pastPath z s) (fun ω => value z t ω-value z s ω) (pastPath_measurable z hz s)
    ((process_measurable z hz t).sub (process_measurable z hz s))
    (past_increment_independent μ z hz s t hst) G hG.stronglyMeasurable hi
  rw [hfun,← history_eq_past z hz s,increment_law μ z hz s t hst] at he
  filter_upwards [he] with ω he
  rw [he]
  have hm : AEStronglyMeasurable (fun y : ℂ => F (value z s ω+y))
      ((probability μ).map (value z (t-s))) :=
    (hF.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  exact integral_map (μ := probability μ) (process_measurable z hz (t-s : ℝ≥0)).aemeasurable hm

theorem observable_integrable (μ : Measure A) [IsProbabilityMeasure μ]
    (z : A → ℂ) (hz : Measurable z) (t : ℝ≥0) (F : ℂ → ℂ) (hF : Measurable F)
    (C : ℝ) (hb : ∀ x, ‖F x‖ ≤ C) :
    Integrable (fun ω => F (value z t ω)) (probability μ) :=
  Integrable.of_bound (hF.comp (process_measurable z hz t)).aestronglyMeasurable C
    (Eventually.of_forall fun ω => hb _)

theorem conditional_transition_bounded (μ : Measure A) [IsProbabilityMeasure μ]
    (z : A → ℂ) (hz : Measurable z) (s t : ℝ≥0) (hst : s ≤ t)
    (F : ℂ → ℂ) (hF : Measurable F) (C : ℝ) (hb : ∀ x, ‖F x‖ ≤ C) :
    (probability μ)[fun ω => F (value z t ω) | history z hz s] =ᵐ[probability μ]
      fun ω => transition μ z (t-s) F (value z s ω) :=
  conditional_transition μ z hz s t hst F hF (observable_integrable μ z hz t F hF C hb)

end OperatorDerivativeRewrite.Foundation.MarkedRealizationMarkov
