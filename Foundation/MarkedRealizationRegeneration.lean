import Foundation.MarkedConditionalRealization
import Foundation.RenewalConditionalFuturePath

/-! Whole actual complex increment paths regenerate under wall-clock count conditioning. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedRealizationRegeneration
open MarkedRenewalRealization MarkedConditionalRealization ExponentialNonexplosiveClock
variable {A : Type*} [MeasurableSpace A]
variable (μ : Measure A) [IsProbabilityMeasure μ]
open ExponentialRenewalCount

abbrev ProcessPath := ℝ≥0 → ℂ
def path (z : A → ℂ) (ω : Sample A) : ProcessPath := fun t => process z t ω
def futurePath (z : A → ℂ) (s : ℝ) (ω : Sample A) : ProcessPath :=
  fun t => process z (s+t) ω-process z s ω

theorem path_measurable (z : A → ℂ) (hz : Measurable z) : Measurable (path z) :=
  measurable_pi_iff.mpr (fun t => process_measurable z hz t)

theorem futurePath_measurable (z : A → ℂ) (hz : Measurable z) (s : ℝ) : Measurable (futurePath z s) :=
  measurable_pi_iff.mpr (fun t => (process_measurable z hz (s+t)).sub (process_measurable z hz s))

theorem process_shift_eq (z : A → ℂ) (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (ω : Sample A)
    (hω : Good ω.1) (hn : count s ω.1 = n)
    (hf : Good (RenewalFreshFutureSource.fresh n s ω.1)) (t : ℝ≥0) :
    process z (s+t) ω-process z s ω = process z t (fresh n s ω) := by
  have he := RenewalConditionalFuturePath.count_shift_eq hω n s hs hn hf t t.coe_nonneg
  change position z (count (s+t) ω.1) ω.2-position z (count s ω.1) ω.2 =
    position z (count t (RenewalFreshFutureSource.fresh n s ω.1))
      (MarkedSourceRegeneration.tail n ω.2)
  rw [he,hn,MarkedSourceRegeneration.position_increment]

theorem futurePath_eq_fresh (z : A → ℂ) (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    futurePath z s =ᵐ[condition μ n s] path z ∘ fresh n s := by
  have ha : condition μ n s ≪ probability μ := cond_absolutelyContinuous
  have hm : ∀ᵐ ω ∂condition μ n s, ω ∈ event n s := ae_cond_mem (event_measurable n s)
  have hf := (fresh_preserving μ n s hs hp).quasiMeasurePreserving.ae (clock_good_ae μ)
  filter_upwards [ha.ae_le (clock_good_ae μ),hm,hf] with ω hω hn hf
  funext t
  exact process_shift_eq z n s hs ω hω hn hf t

theorem future_preserving (z : A → ℂ) (hz : Measurable z) (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    MeasurePreserving (futurePath z s) (condition μ n s) ((probability μ).map (path z)) := by
  refine ⟨futurePath_measurable z hz s, ?_⟩
  rw [Measure.map_congr (futurePath_eq_fresh μ z n s hs hp)]
  have hl : MeasurePreserving (path z) (probability μ) ((probability μ).map (path z)) :=
    ⟨path_measurable z hz,rfl⟩
  exact (hl.comp (fresh_preserving μ n s hs hp)).map_eq

theorem past_future_independent (z : A → ℂ) (hz : Measurable z) (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    IndepFun (past n) (futurePath z s) (condition μ n s) := by
  have hi := (past_fresh_independent μ n s hs hp).comp measurable_id (path_measurable z hz)
  exact hi.congr (Eventually.of_forall (fun _ => rfl)) (futurePath_eq_fresh μ z n s hs hp).symm

theorem past_future_preserving (z : A → ℂ) (hz : Measurable z) (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    MeasurePreserving (fun ω => (past n ω,futurePath z s ω)) (condition μ n s)
      ((pastLaw μ n s).prod ((probability μ).map (path z))) := by
  have : IsProbabilityMeasure (condition μ n s) := condition_probability μ n s hp
  refine ⟨(past_measurable n).prodMk (futurePath_measurable z hz s), ?_⟩
  rw [(past_future_independent μ z hz n s hs hp).map_prod_eq_prod_map_map
    (past_measurable n).aemeasurable (futurePath_measurable z hz s).aemeasurable,
    (past_preserving μ n s hs hp).map_eq,(future_preserving μ z hz n s hs hp).map_eq]


end OperatorDerivativeRewrite.Foundation.MarkedRealizationRegeneration
