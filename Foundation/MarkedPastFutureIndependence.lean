import Foundation.MarkedPastReconstruction
import Foundation.CountableConditionalIndependence

/-! Actual entire marked past and future increment paths have a joint product law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedPastFutureIndependence
open MarkedRootRenewalProcess MarkedConditionalSource MarkedRenewalRegeneration
open MarkedPastReconstruction ExponentialRenewalCount

theorem past_future_joint_law (a : ℝ) (s : ℝ≥0) :
    probability.map (fun ω => (pastPath a s ω,futurePath a s ω)) =
      (probability.map (pastPath a s)).prod (probability.map (path a)) := by
  have hc : Measurable (fun ω : StateSample => count s ω.1) :=
    (count_measurable s).comp measurable_fst
  apply CountableConditionalIndependence.joint_law probability (probability.map (path a))
    (fun ω : StateSample => count s ω.1) hc (pastPath a s) (futurePath a s)
    (pastPath_measurable a s) (futurePath_measurable a s)
  · intro n hp
    have he : (fun ω : StateSample => count s ω.1) ⁻¹' {n} = event n s := by
      ext ω
      simp [MarkedConditionalSource.event,RenewalConditionalResidual.event]
    rw [he] at hp ⊢
    have hh : ExponentialHoldingSequence.probability
        (RenewalConditionalResidual.event n s) ≠ 0 := by
      rwa [← event_measure n s]
    exact (future_preserving a n s s.coe_nonneg hh).map_eq
  · intro n hp
    have he : (fun ω : StateSample => count s ω.1) ⁻¹' {n} = event n s := by
      ext ω
      simp [MarkedConditionalSource.event,RenewalConditionalResidual.event]
    rw [he] at hp ⊢
    have hh : ExponentialHoldingSequence.probability
        (RenewalConditionalResidual.event n s) ≠ 0 := by
      rwa [← event_measure n s]
    exact conditional_past_future_independent a n s hh

theorem future_law (a : ℝ) (s : ℝ≥0) :
    probability.map (futurePath a s) = probability.map (path a) := by
  have he := congrArg (fun μ : Measure (PastPath s × ProcessPath) => μ.map Prod.snd)
    (past_future_joint_law a s)
  rw [Measure.map_map measurable_snd ((pastPath_measurable a s).prodMk (futurePath_measurable a s)),
    Measure.map_snd_prod,measure_univ,one_smul] at he
  exact he

theorem past_future_independent (a : ℝ) (s : ℝ≥0) :
    IndepFun (pastPath a s) (futurePath a s) probability := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (pastPath_measurable a s).aemeasurable (futurePath_measurable a s).aemeasurable).mpr
  rw [future_law]
  exact past_future_joint_law a s

theorem future_preserving (a : ℝ) (s : ℝ≥0) :
    MeasurePreserving (futurePath a s) probability (probability.map (path a)) :=
  ⟨futurePath_measurable a s,future_law a s⟩

theorem increment_law (a : ℝ) (s h : ℝ≥0) :
    probability.map (fun ω => process a (s+h : ℝ≥0) ω-process a s ω) =
      ComplexRootPoissonLaw.law h a := by
  have he := congrArg (fun μ : Measure ProcessPath => μ.map (fun γ => γ h)) (future_law a s)
  rw [Measure.map_map (measurable_pi_apply h) (futurePath_measurable a s),
    Measure.map_map (measurable_pi_apply h) (path_measurable a)] at he
  have hf : (fun ω => process a (s+h : ℝ≥0) ω-process a s ω) =
      (fun γ : ProcessPath => γ h) ∘ futurePath a s := by
    funext ω
    simp only [Function.comp_def,futurePath,NNReal.coe_add]
  rw [hf,he]
  exact ConstructedRenewalPoissonLaw.process_law_eq_poisson a h

end OperatorDerivativeRewrite.Foundation.MarkedPastFutureIndependence
