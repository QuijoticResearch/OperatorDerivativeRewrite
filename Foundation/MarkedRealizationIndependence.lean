import Foundation.MarkedRealizationPast
import Foundation.CountableConditionalIndependence

/-! Entire past/future independence on the actual general marked-renewal probability source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedRealizationIndependence
open MarkedRenewalRealization MarkedConditionalRealization MarkedRealizationRegeneration
open MarkedRealizationPast ExponentialRenewalCount
variable {A : Type*} [MeasurableSpace A]
variable (μ : Measure A) [IsProbabilityMeasure μ]

theorem past_future_joint_law (z : A → ℂ) (hz : Measurable z) (s : ℝ≥0) :
    (probability μ).map (fun ω => (pastPath z s ω,futurePath z s ω)) =
      ((probability μ).map (pastPath z s)).prod ((probability μ).map (path z)) := by
  have hc : Measurable (fun ω : Sample A => count s ω.1) :=
    (count_measurable s).comp measurable_fst
  apply CountableConditionalIndependence.joint_law (probability μ) ((probability μ).map (path z))
    (fun ω : Sample A => count s ω.1) hc (pastPath z s) (futurePath z s)
    (pastPath_measurable z hz s) (futurePath_measurable z hz s)
  · intro n hp
    have he : (fun ω : Sample A => count s ω.1) ⁻¹' {n} = event n s := by
      ext ω
      simp [MarkedConditionalRealization.event,RenewalConditionalResidual.event]
    rw [he] at hp ⊢
    have hh : ExponentialHoldingSequence.probability
        (RenewalConditionalResidual.event n s) ≠ 0 := by
      rwa [← event_measure μ n s]
    exact (future_preserving μ z hz n s s.coe_nonneg hh).map_eq
  · intro n hp
    have he : (fun ω : Sample A => count s ω.1) ⁻¹' {n} = event n s := by
      ext ω
      simp [MarkedConditionalRealization.event,RenewalConditionalResidual.event]
    rw [he] at hp ⊢
    have hh : ExponentialHoldingSequence.probability
        (RenewalConditionalResidual.event n s) ≠ 0 := by
      rwa [← event_measure μ n s]
    exact conditional_past_future_independent μ z hz n s hh

theorem future_law (z : A → ℂ) (hz : Measurable z) (s : ℝ≥0) :
    (probability μ).map (futurePath z s) = (probability μ).map (path z) := by
  have he := congrArg (fun ν : Measure (PastPath s × ProcessPath) => ν.map Prod.snd)
    (past_future_joint_law μ z hz s)
  rw [Measure.map_map measurable_snd ((pastPath_measurable z hz s).prodMk
      (futurePath_measurable z hz s)),Measure.map_snd_prod,measure_univ,one_smul] at he
  exact he

theorem past_future_independent (z : A → ℂ) (hz : Measurable z) (s : ℝ≥0) :
    IndepFun (pastPath z s) (futurePath z s) (probability μ) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (pastPath_measurable z hz s).aemeasurable (futurePath_measurable z hz s).aemeasurable).mpr
  rw [future_law μ z hz s]
  exact past_future_joint_law μ z hz s

theorem future_preserving (z : A → ℂ) (hz : Measurable z) (s : ℝ≥0) :
    MeasurePreserving (futurePath z s) (probability μ) ((probability μ).map (path z)) :=
  ⟨futurePath_measurable z hz s,future_law μ z hz s⟩

end OperatorDerivativeRewrite.Foundation.MarkedRealizationIndependence
