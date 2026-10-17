import Foundation.AdaptiveExponentialResidual
import Foundation.ExponentialSourceRegeneration

/-! Actual holding history and the unfinished next holding time at a fixed observation time. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace OperatorDerivativeRewrite.Foundation.RenewalWallClockResidual
open ExponentialHoldingSequence ExponentialNonexplosiveClock ExponentialRenewalCount

def elapsed (n : ℕ) (ξ : FiniteExponentialRenewal.Sample n) : ℝ := ∑ i, ξ i
def complete (n : ℕ) (s : ℝ) : Set (FiniteExponentialRenewal.Sample n) := {ξ | elapsed n ξ ≤ s}
def threshold (n : ℕ) (s : ℝ) (ξ : FiniteExponentialRenewal.Sample n) : ℝ := max (s-elapsed n ξ) 0
def pair (n : ℕ) (ω : Sample) : FiniteExponentialRenewal.Sample n × ℝ :=
  (ConstructedRenewalPoissonLaw.initialSegment n ω,holding n ω)
def cylinder (n : ℕ) (s : ℝ) : Set (FiniteExponentialRenewal.Sample n × ℝ) :=
  AdaptiveExponentialResidual.survive (threshold n s) ∩ (complete n s ×ˢ univ)
def historyResidual (n : ℕ) (s : ℝ) := AdaptiveExponentialResidual.shift (threshold n s) ∘ pair n
def historyLaw (n : ℕ) (s : ℝ) : Measure (FiniteExponentialRenewal.Sample n) :=
  AdaptiveExponentialResidual.past
    ((FiniteExponentialRenewal.probability n).restrict (complete n s))
    (threshold n s)

theorem elapsed_measurable (n : ℕ) : Measurable (elapsed n) := by unfold elapsed; fun_prop
theorem complete_measurable (n : ℕ) (s : ℝ) : MeasurableSet (complete n s) :=
  measurableSet_le (elapsed_measurable n) measurable_const
theorem threshold_measurable (n : ℕ) (s : ℝ) : Measurable (threshold n s) :=
  (measurable_const.sub (elapsed_measurable n)).max measurable_const

theorem pair_measurable (n : ℕ) : Measurable (pair n) :=
  (ConstructedRenewalPoissonLaw.initialSegment_measurable n).prodMk (holding_measurable n)

theorem pair_preserving (n : ℕ) :
    MeasurePreserving (pair n) probability
      ((FiniteExponentialRenewal.probability n).prod base) := by
  have hi := (ExponentialSourceRegeneration.past_tail_independent n).comp
    measurable_id (measurable_pi_apply 0)
  have hin : IndepFun (ConstructedRenewalPoissonLaw.initialSegment n) (holding n) probability := by
    simpa only [ExponentialSourceRegeneration.tail, Function.comp_def, Nat.add_zero, id_eq] using hi
  refine ⟨pair_measurable n, ?_⟩
  change probability.map
    (fun ω => (ConstructedRenewalPoissonLaw.initialSegment n ω,holding n ω)) = _
  rw [hin.map_prod_eq_prod_map_map
    (ConstructedRenewalPoissonLaw.initialSegment_measurable n).aemeasurable
    (holding_measurable n).aemeasurable,
    (ConstructedRenewalPoissonLaw.initialSegment_preserving n).map_eq, holding_law]

theorem elapsed_initialSegment (n : ℕ) (ω : Sample) :
    elapsed n (ConstructedRenewalPoissonLaw.initialSegment n ω) = clock n ω := by
  unfold elapsed ConstructedRenewalPoissonLaw.initialSegment clock
  exact Fin.sum_univ_eq_sum_range (fun i => holding i ω) n

theorem cylinder_measurable (n : ℕ) (s : ℝ) : MeasurableSet (cylinder n s) :=
  (AdaptiveExponentialResidual.survive_measurable (threshold_measurable n s)).inter
    ((complete_measurable n s).prod MeasurableSet.univ)

theorem count_event (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    {ω | count s ω = n} =ᵐ[probability] (pair n) ⁻¹' cylinder n s := by
  filter_upwards [good_ae] with ω hω
  apply propext
  rw [ConstructedRenewalPoissonLaw.count_eq_iff hω s hs n, clock_successor]
  change (clock n ω ≤ s ∧ s < clock n ω + holding n ω) ↔
    (max (s-elapsed n (ConstructedRenewalPoissonLaw.initialSegment n ω)) 0 < holding n ω ∧
      elapsed n (ConstructedRenewalPoissonLaw.initialSegment n ω) ≤ s ∧ True)
  rw [elapsed_initialSegment]
  constructor
  · intro h
    rw [max_eq_left (sub_nonneg.mpr h.1)]
    exact ⟨by linarith [h.2],h.1,trivial⟩
  · intro h
    rw [max_eq_left (sub_nonneg.mpr h.2.1)] at h
    exact ⟨h.2.1,by linarith [h.1]⟩

theorem historyResidual_measurable (n : ℕ) (s : ℝ) : Measurable (historyResidual n s) :=
  (AdaptiveExponentialResidual.shift_measurable (threshold_measurable n s)).comp (pair_measurable n)

theorem restricted_joint_law (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (probability.restrict {ω | count s ω = n}).map (historyResidual n s) =
      (historyLaw n s).prod base := by
  rw [Measure.restrict_congr_set (count_event n s hs), historyResidual,
    ← Measure.map_map (AdaptiveExponentialResidual.shift_measurable (threshold_measurable n s))
      (pair_measurable n), ← Measure.restrict_map (pair_measurable n) (cylinder_measurable n s),
    (pair_preserving n).map_eq]
  have he : ((FiniteExponentialRenewal.probability n).prod base).restrict (cylinder n s) =
      (((FiniteExponentialRenewal.probability n).restrict (complete n s)).prod base).restrict
        (AdaptiveExponentialResidual.survive (threshold n s)) := by
    rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_restrict
      (AdaptiveExponentialResidual.survive_measurable (threshold_measurable n s))]
    rfl
  rw [he]
  exact AdaptiveExponentialResidual.joint_law _ _ (threshold_measurable n s)
    (fun ξ => le_max_right _ _)

theorem historyResidual_on_event (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ∀ᵐ ω ∂probability, count s ω = n →
      historyResidual n s ω =
        (ConstructedRenewalPoissonLaw.initialSegment n ω,clock (n+1) ω-s) := by
  filter_upwards [good_ae] with ω hω hn
  have hbefore := ((ConstructedRenewalPoissonLaw.count_eq_iff hω s hs n).mp hn).1
  change (ConstructedRenewalPoissonLaw.initialSegment n ω,
    holding n ω - max (s-elapsed n (ConstructedRenewalPoissonLaw.initialSegment n ω)) 0) = _
  rw [elapsed_initialSegment, max_eq_left (sub_nonneg.mpr hbefore), clock_successor]
  congr 1
  ring

end OperatorDerivativeRewrite.Foundation.RenewalWallClockResidual
