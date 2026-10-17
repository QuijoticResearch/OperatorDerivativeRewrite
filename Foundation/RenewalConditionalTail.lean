import Foundation.IndependentPastConditioning
import Foundation.RenewalConditionalResidual

/-! The actual untouched infinite holding tail remains independent after observing the count. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace OperatorDerivativeRewrite.Foundation.RenewalConditionalTail
open ExponentialHoldingSequence ExponentialNonexplosiveClock ExponentialRenewalCount
open RenewalConditionalResidual ExponentialSourceRegeneration

theorem count_event_prefix (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    event n s =ᵐ[probability] (ConstructedRenewalPoissonLaw.initialSegment (n+1)) ⁻¹'
      FiniteExponentialRenewal.event n s := by
  filter_upwards [good_ae] with ω hω
  apply propext
  change count s ω = n ↔ _
  rw [ConstructedRenewalPoissonLaw.count_eq_iff hω s hs n]
  change _ ↔ FiniteExponentialRenewal.partialSum n
    (ConstructedRenewalPoissonLaw.initialSegment (n+1) ω) ≤ s ∧
      s < FiniteExponentialRenewal.total n (ConstructedRenewalPoissonLaw.initialSegment (n+1) ω)
  rw [ConstructedRenewalPoissonLaw.partial_initialSegment,
    ConstructedRenewalPoissonLaw.total_initialSegment]

theorem condition_eq_prefix (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    condition n s = cond probability ((ConstructedRenewalPoissonLaw.initialSegment (n+1)) ⁻¹'
      FiniteExponentialRenewal.event n s) :=
  IndependentPastConditioning.cond_congr probability (count_event_prefix n s hs)

theorem tail_law (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (hp : probability (event n s) ≠ 0) :
    (condition n s).map (tail (n+1)) = probability := by
  have hn : probability ((ConstructedRenewalPoissonLaw.initialSegment (n+1)) ⁻¹'
      FiniteExponentialRenewal.event n s) ≠ 0 := by
    rwa [← measure_congr (count_event_prefix n s hs)]
  rw [condition_eq_prefix n s hs,
    IndependentPastConditioning.future_law
      (ConstructedRenewalPoissonLaw.initialSegment_measurable (n+1)) (tail_measurable (n+1))
      (past_tail_independent (n+1)) _ (FiniteExponentialRenewal.event_measurable n s) hn,
    (tail_preserving (n+1)).map_eq]

theorem prefix_tail_independent (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : probability (event n s) ≠ 0) :
    IndepFun (ConstructedRenewalPoissonLaw.initialSegment (n+1)) (tail (n+1)) (condition n s) := by
  have hn : probability ((ConstructedRenewalPoissonLaw.initialSegment (n+1)) ⁻¹'
      FiniteExponentialRenewal.event n s) ≠ 0 := by
    rwa [← measure_congr (count_event_prefix n s hs)]
  rw [condition_eq_prefix n s hs]
  exact IndependentPastConditioning.conditional_independent
    (ConstructedRenewalPoissonLaw.initialSegment_measurable (n+1)) (tail_measurable (n+1))
    (past_tail_independent (n+1)) _ (FiniteExponentialRenewal.event_measurable n s) hn

def project (n : ℕ) (s : ℝ) (ξ : FiniteExponentialRenewal.Sample (n + 1)) :
    FiniteExponentialRenewal.Sample n × ℝ :=
  (fun i => ξ i.castSucc,FiniteExponentialRenewal.total n ξ-s)

theorem project_measurable (n : ℕ) (s : ℝ) : Measurable (project n s) := by
  have hp : Measurable (fun ξ : FiniteExponentialRenewal.Sample (n+1) =>
      fun i : Fin n => ξ i.castSucc) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply i.castSucc)
  have ht : Measurable (fun ξ : FiniteExponentialRenewal.Sample (n+1) =>
      FiniteExponentialRenewal.total n ξ-s) := by unfold FiniteExponentialRenewal.total; fun_prop
  exact hp.prodMk ht

theorem observation_eq_project (n : ℕ) (s : ℝ) :
    observation n s = project n s ∘ ConstructedRenewalPoissonLaw.initialSegment (n+1) := by
  funext ω
  apply Prod.ext
  · rfl
  · change clock (n+1) ω-s = FiniteExponentialRenewal.total n
      (ConstructedRenewalPoissonLaw.initialSegment (n+1) ω)-s
    rw [ConstructedRenewalPoissonLaw.total_initialSegment]

theorem observation_tail_independent (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : probability (event n s) ≠ 0) :
    IndepFun (observation n s) (tail (n+1)) (condition n s) := by
  rw [observation_eq_project]
  have he := (prefix_tail_independent n s hs hp).comp (project_measurable n s) measurable_id
  simpa only [Function.comp_def, id_eq] using he

theorem observation_tail_law (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : probability (event n s) ≠ 0) :
    (condition n s).map (fun ω => (observation n s ω,tail (n+1) ω)) =
      ((history n s).prod base).prod probability := by
  have : IsProbabilityMeasure (condition n s) := conditional_probability n s hp
  rw [(observation_tail_independent n s hs hp).map_prod_eq_prod_map_map
    (observation_measurable n s).aemeasurable (tail_measurable (n+1)).aemeasurable,
    conditional_joint_law n s hs, tail_law n s hs hp]

end OperatorDerivativeRewrite.Foundation.RenewalConditionalTail
