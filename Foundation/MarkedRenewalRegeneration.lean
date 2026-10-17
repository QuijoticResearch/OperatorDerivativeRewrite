import Foundation.MarkedConditionalSource
import Foundation.RenewalConditionalFuturePath

/-! Whole actual complex increment paths regenerate under wall-clock count conditioning. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedRenewalRegeneration
open MarkedRootRenewalProcess MarkedConditionalSource ExponentialNonexplosiveClock
open ExponentialRenewalCount

abbrev ProcessPath := ℝ≥0 → ℂ
def path (a : ℝ) (ω : StateSample) : ProcessPath := fun t => process a t ω
def futurePath (a s : ℝ) (ω : StateSample) : ProcessPath :=
  fun t => process a (s+t) ω-process a s ω

theorem path_measurable (a : ℝ) : Measurable (path a) :=
  measurable_pi_iff.mpr (fun t => process_measurable a t)

theorem futurePath_measurable (a s : ℝ) : Measurable (futurePath a s) :=
  measurable_pi_iff.mpr (fun t => (process_measurable a (s+t)).sub (process_measurable a s))

theorem process_shift_eq (a : ℝ) (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (ω : StateSample)
    (hω : Good ω.1) (hn : count s ω.1 = n)
    (hf : Good (RenewalFreshFutureSource.fresh n s ω.1)) (t : ℝ≥0) :
    process a (s+t) ω-process a s ω = process a t (fresh n s ω) := by
  have he := RenewalConditionalFuturePath.count_shift_eq hω n s hs hn hf t t.coe_nonneg
  change position a (count (s+t) ω.1) ω.2-position a (count s ω.1) ω.2 =
    position a (count t (RenewalFreshFutureSource.fresh n s ω.1))
      (RootMarkSourceRegeneration.tail n ω.2)
  rw [he,hn,RootMarkSourceRegeneration.position_increment]

theorem futurePath_eq_fresh (a : ℝ) (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    futurePath a s =ᵐ[condition n s] path a ∘ fresh n s := by
  have ha : condition n s ≪ probability := cond_absolutelyContinuous
  have hm : ∀ᵐ ω ∂condition n s, ω ∈ event n s := ae_cond_mem (event_measurable n s)
  have hf := (fresh_preserving n s hs hp).quasiMeasurePreserving.ae clock_good_ae
  filter_upwards [ha.ae_le clock_good_ae,hm,hf] with ω hω hn hf
  funext t
  exact process_shift_eq a n s hs ω hω hn hf t

theorem future_preserving (a : ℝ) (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    MeasurePreserving (futurePath a s) (condition n s) (probability.map (path a)) := by
  refine ⟨futurePath_measurable a s, ?_⟩
  rw [Measure.map_congr (futurePath_eq_fresh a n s hs hp)]
  have hl : MeasurePreserving (path a) probability (probability.map (path a)) :=
    ⟨path_measurable a,rfl⟩
  exact (hl.comp (fresh_preserving n s hs hp)).map_eq

theorem past_future_independent (a : ℝ) (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    IndepFun (past n) (futurePath a s) (condition n s) := by
  have hi := (past_fresh_independent n s hs hp).comp measurable_id (path_measurable a)
  exact hi.congr (Eventually.of_forall (fun _ => rfl)) (futurePath_eq_fresh a n s hs hp).symm

theorem past_future_preserving (a : ℝ) (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    MeasurePreserving (fun ω => (past n ω,futurePath a s ω)) (condition n s)
      ((pastLaw n s).prod (probability.map (path a))) := by
  have : IsProbabilityMeasure (condition n s) := condition_probability n s hp
  refine ⟨(past_measurable n).prodMk (futurePath_measurable a s), ?_⟩
  rw [(past_future_independent a n s hs hp).map_prod_eq_prod_map_map
    (past_measurable n).aemeasurable (futurePath_measurable a s).aemeasurable,
    (past_preserving n s hs hp).map_eq,(future_preserving a n s hs hp).map_eq]

theorem increment_law (a : ℝ) (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0)
    (h : ℝ≥0) :
    (condition n s).map (fun ω => process a (s+h) ω-process a s ω) =
      ComplexRootPoissonLaw.law h a := by
  have he := congrArg (fun μ : Measure ProcessPath => μ.map (fun γ => γ h))
    (future_preserving a n s hs hp).map_eq
  rw [Measure.map_map (measurable_pi_apply h) (futurePath_measurable a s),
    Measure.map_map (measurable_pi_apply h) (path_measurable a)] at he
  have hf : (fun ω => process a (s+h) ω-process a s ω) =
      (fun γ : ProcessPath => γ h) ∘ futurePath a s := rfl
  rw [hf,he]
  exact ConstructedRenewalPoissonLaw.process_law_eq_poisson a h

end OperatorDerivativeRewrite.Foundation.MarkedRenewalRegeneration
