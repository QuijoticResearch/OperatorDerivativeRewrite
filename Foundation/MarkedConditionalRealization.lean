import Foundation.MarkedSourceRegeneration
import Foundation.ProductSourceShuffle
import Foundation.RenewalFreshFutureSource

/-! Actual conditional marked sources split into a completed past and a fresh independent source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace OperatorDerivativeRewrite.Foundation.MarkedConditionalRealization
open MarkedRenewalRealization FiniteMarkedRenewalMarginals
variable {A : Type*} [MeasurableSpace A]
variable (μ : Measure A) [IsProbabilityMeasure μ]

abbrev PastState (A : Type*) (n : ℕ) := FiniteExponentialRenewal.Sample n × Prefix A n
def event (n : ℕ) (s : ℝ) : Set (Sample A) :=
  Prod.fst ⁻¹' RenewalConditionalResidual.event n s
def condition (μ : Measure A) (n : ℕ) (s : ℝ) : Measure (Sample A) := cond (probability μ) (event n s)
def past (n : ℕ) (ω : Sample A) : PastState A n :=
  (ConstructedRenewalPoissonLaw.initialSegment n ω.1,initialSegment n ω.2)
def pastLaw (μ : Measure A) (n : ℕ) (s : ℝ) : Measure (PastState A n) :=
  (RenewalConditionalResidual.history n s).prod (finiteProbability μ n)
def fresh (n : ℕ) (s : ℝ) (ω : Sample A) : Sample A :=
  (RenewalFreshFutureSource.fresh n s ω.1,MarkedSourceRegeneration.tail n ω.2)

theorem event_measurable (n : ℕ) (s : ℝ) : MeasurableSet (event (A := A) n s) :=
  measurable_fst (RenewalConditionalResidual.event_measurable n s)

theorem event_measure (n : ℕ) (s : ℝ) : probability μ (event n s) =
    ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) := by
  have he : (probability μ).map (Prod.fst : Sample A → ExponentialHoldingSequence.Sample) =
      ExponentialHoldingSequence.probability := measurePreserving_fst.map_eq
  have he' := congrArg (fun μ : Measure ExponentialHoldingSequence.Sample =>
    μ (RenewalConditionalResidual.event n s)) he
  rw [Measure.map_apply measurable_fst (RenewalConditionalResidual.event_measurable n s)] at he'
  exact he'

theorem condition_eq_product (n : ℕ) (s : ℝ) :
    condition μ n s = (RenewalConditionalResidual.condition n s).prod (marks μ) := by
  have he := IndependentPastConditioning.conditional_joint (μ := probability μ)
    measurable_fst measurable_snd (sources_independent μ)
    (RenewalConditionalResidual.event n s) (RenewalConditionalResidual.event_measurable n s)
  have hf : (probability μ).map (Prod.fst : Sample A → ExponentialHoldingSequence.Sample) =
      ExponentialHoldingSequence.probability := measurePreserving_fst.map_eq
  have hg : (probability μ).map (Prod.snd : Sample A → MarkSample A) = marks μ :=
    measurePreserving_snd.map_eq
  rw [show (fun ω : Sample A => (ω.1,ω.2)) = id from rfl, Measure.map_id,hf,hg] at he
  exact he

theorem past_measurable (n : ℕ) : Measurable (past (A := A) n) :=
  ((ConstructedRenewalPoissonLaw.initialSegment_measurable n).comp measurable_fst).prodMk
    ((prefix_measurable n).comp measurable_snd)

theorem fresh_measurable (n : ℕ) (s : ℝ) : Measurable (fresh (A := A) n s) :=
  ((RenewalFreshFutureSource.fresh_measurable n s).comp measurable_fst).prodMk
    ((MarkedSourceRegeneration.tail_measurable n).comp measurable_snd)

theorem condition_probability (n : ℕ) (s : ℝ)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    IsProbabilityMeasure (condition μ n s) := by
  rw [condition_eq_product μ]
  have : IsProbabilityMeasure (RenewalConditionalResidual.condition n s) :=
    RenewalConditionalResidual.conditional_probability n s hp
  infer_instance

theorem past_probability (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    IsProbabilityMeasure (pastLaw μ n s) := by
  unfold pastLaw
  have : IsProbabilityMeasure (RenewalConditionalResidual.history n s) :=
    RenewalConditionalResidual.history_probability n s hs hp
  infer_instance

theorem split_preserving (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    MeasurePreserving (fun ω => (past n ω,fresh n s ω)) (condition μ n s)
      ((pastLaw μ n s).prod (probability μ)) := by
  have : IsProbabilityMeasure (RenewalConditionalResidual.condition n s) :=
    RenewalConditionalResidual.conditional_probability n s hp
  have : IsProbabilityMeasure (RenewalConditionalResidual.history n s) :=
    RenewalConditionalResidual.history_probability n s hs hp
  have he := (ProductSourceShuffle.preserving (RenewalConditionalResidual.history n s)
    ExponentialHoldingSequence.probability (finiteProbability μ n) (marks μ)).comp
    ((RenewalFreshFutureSource.past_fresh_preserving n s hs hp).prod
      (MarkedSourceRegeneration.split_preserving μ n))
  rw [condition_eq_product μ]
  exact he

theorem fresh_preserving (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    MeasurePreserving (fresh n s) (condition μ n s) (probability μ) := by
  have : IsProbabilityMeasure (pastLaw μ n s) := past_probability μ n s hs hp
  exact measurePreserving_snd.comp (split_preserving μ n s hs hp)

theorem past_preserving (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    MeasurePreserving (past n) (condition μ n s) (pastLaw μ n s) :=
  measurePreserving_fst.comp (split_preserving μ n s hs hp)

theorem past_fresh_independent (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    IndepFun (past n) (fresh n s) (condition μ n s) := by
  have : IsProbabilityMeasure (condition μ n s) := condition_probability μ n s hp
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (past_measurable n).aemeasurable (fresh_measurable n s).aemeasurable).mpr
  rw [(past_preserving μ n s hs hp).map_eq,(fresh_preserving μ n s hs hp).map_eq]
  exact (split_preserving μ n s hs hp).map_eq

end OperatorDerivativeRewrite.Foundation.MarkedConditionalRealization
