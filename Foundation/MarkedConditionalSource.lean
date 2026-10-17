import Foundation.RootMarkSourceRegeneration
import Foundation.ProductSourceShuffle
import Foundation.RenewalFreshFutureSource

/-! Actual conditional marked sources split into a completed past and a fresh independent source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace OperatorDerivativeRewrite.Foundation.MarkedConditionalSource
open MarkedRootRenewalProcess

abbrev PastState (n : ℕ) := FiniteExponentialRenewal.Sample n × ComplexFourthRootWalk.Sample n
def event (n : ℕ) (s : ℝ) : Set StateSample :=
  Prod.fst ⁻¹' RenewalConditionalResidual.event n s
def condition (n : ℕ) (s : ℝ) : Measure StateSample := cond probability (event n s)
def past (n : ℕ) (ω : StateSample) : PastState n :=
  (ConstructedRenewalPoissonLaw.initialSegment n ω.1,RootRenewalWalkMarginal.initialSegment n ω.2)
def pastLaw (n : ℕ) (s : ℝ) : Measure (PastState n) :=
  (RenewalConditionalResidual.history n s).prod (ComplexFourthRootWalk.probability n)
def fresh (n : ℕ) (s : ℝ) (ω : StateSample) : StateSample :=
  (RenewalFreshFutureSource.fresh n s ω.1,RootMarkSourceRegeneration.tail n ω.2)

theorem event_measurable (n : ℕ) (s : ℝ) : MeasurableSet (event n s) :=
  measurable_fst (RenewalConditionalResidual.event_measurable n s)

theorem event_measure (n : ℕ) (s : ℝ) : probability (event n s) =
    ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) := by
  have he : probability.map (Prod.fst : StateSample → ExponentialHoldingSequence.Sample) =
      ExponentialHoldingSequence.probability := measurePreserving_fst.map_eq
  have he' := congrArg (fun μ : Measure ExponentialHoldingSequence.Sample =>
    μ (RenewalConditionalResidual.event n s)) he
  rw [Measure.map_apply measurable_fst (RenewalConditionalResidual.event_measurable n s)] at he'
  exact he'

theorem condition_eq_product (n : ℕ) (s : ℝ) :
    condition n s = (RenewalConditionalResidual.condition n s).prod marks := by
  have he := IndependentPastConditioning.conditional_joint (μ := probability)
    measurable_fst measurable_snd sources_independent
    (RenewalConditionalResidual.event n s) (RenewalConditionalResidual.event_measurable n s)
  have hf : probability.map (Prod.fst : StateSample → ExponentialHoldingSequence.Sample) =
      ExponentialHoldingSequence.probability := measurePreserving_fst.map_eq
  have hg : probability.map (Prod.snd : StateSample → MarkSample) = marks :=
    measurePreserving_snd.map_eq
  rw [show (fun ω : StateSample => (ω.1,ω.2)) = id from rfl, Measure.map_id,hf,hg] at he
  exact he

theorem past_measurable (n : ℕ) : Measurable (past n) :=
  ((ConstructedRenewalPoissonLaw.initialSegment_measurable n).comp measurable_fst).prodMk
    ((RootRenewalWalkMarginal.prefix_measurable n).comp measurable_snd)

theorem fresh_measurable (n : ℕ) (s : ℝ) : Measurable (fresh n s) :=
  ((RenewalFreshFutureSource.fresh_measurable n s).comp measurable_fst).prodMk
    ((RootMarkSourceRegeneration.tail_measurable n).comp measurable_snd)

theorem condition_probability (n : ℕ) (s : ℝ)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    IsProbabilityMeasure (condition n s) := by
  rw [condition_eq_product]
  have : IsProbabilityMeasure (RenewalConditionalResidual.condition n s) :=
    RenewalConditionalResidual.conditional_probability n s hp
  infer_instance

theorem past_probability (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    IsProbabilityMeasure (pastLaw n s) := by
  unfold pastLaw
  have : IsProbabilityMeasure (RenewalConditionalResidual.history n s) :=
    RenewalConditionalResidual.history_probability n s hs hp
  infer_instance

theorem split_preserving (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    MeasurePreserving (fun ω => (past n ω,fresh n s ω)) (condition n s)
      ((pastLaw n s).prod probability) := by
  have : IsProbabilityMeasure (RenewalConditionalResidual.condition n s) :=
    RenewalConditionalResidual.conditional_probability n s hp
  have : IsProbabilityMeasure (RenewalConditionalResidual.history n s) :=
    RenewalConditionalResidual.history_probability n s hs hp
  have he := (ProductSourceShuffle.preserving (RenewalConditionalResidual.history n s)
    ExponentialHoldingSequence.probability (ComplexFourthRootWalk.probability n) marks).comp
    ((RenewalFreshFutureSource.past_fresh_preserving n s hs hp).prod
      (RootMarkSourceRegeneration.split_preserving n))
  rw [condition_eq_product]
  exact he

theorem fresh_preserving (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    MeasurePreserving (fresh n s) (condition n s) probability := by
  have : IsProbabilityMeasure (pastLaw n s) := past_probability n s hs hp
  exact measurePreserving_snd.comp (split_preserving n s hs hp)

theorem past_preserving (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    MeasurePreserving (past n) (condition n s) (pastLaw n s) :=
  measurePreserving_fst.comp (split_preserving n s hs hp)

theorem past_fresh_independent (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    IndepFun (past n) (fresh n s) (condition n s) := by
  have : IsProbabilityMeasure (condition n s) := condition_probability n s hp
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (past_measurable n).aemeasurable (fresh_measurable n s).aemeasurable).mpr
  rw [(past_preserving n s hs hp).map_eq,(fresh_preserving n s hs hp).map_eq]
  exact (split_preserving n s hs hp).map_eq

end OperatorDerivativeRewrite.Foundation.MarkedConditionalSource
