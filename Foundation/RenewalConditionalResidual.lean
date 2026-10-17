import Foundation.RenewalWallClockResidual
import Mathlib.Probability.ConditionalProbability

/-! Native conditional laws of actual history and next-arrival residual at a wall-clock time. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.RenewalConditionalResidual
open ExponentialHoldingSequence ExponentialNonexplosiveClock ExponentialRenewalCount

def event (n : ℕ) (s : ℝ) : Set Sample := {ω | count s ω = n}
def condition (n : ℕ) (s : ℝ) : Measure Sample := cond probability (event n s)
def history (n : ℕ) (s : ℝ) : Measure (FiniteExponentialRenewal.Sample n) :=
  (probability (event n s))⁻¹ • RenewalWallClockResidual.historyLaw n s
def remaining (n : ℕ) (s : ℝ) (ω : Sample) : ℝ := clock (n+1) ω-s
def observation (n : ℕ) (s : ℝ) (ω : Sample) : FiniteExponentialRenewal.Sample n × ℝ :=
  (ConstructedRenewalPoissonLaw.initialSegment n ω,remaining n s ω)

theorem event_measurable (n : ℕ) (s : ℝ) : MeasurableSet (event n s) :=
  (count_measurable s) (measurableSet_singleton n)

theorem remaining_measurable (n : ℕ) (s : ℝ) : Measurable (remaining n s) :=
  (clock_measurable (n+1)).sub_const s

theorem observation_measurable (n : ℕ) (s : ℝ) : Measurable (observation n s) :=
  (ConstructedRenewalPoissonLaw.initialSegment_measurable n).prodMk (remaining_measurable n s)

theorem observation_ae (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    RenewalWallClockResidual.historyResidual n s =ᵐ[condition n s] observation n s := by
  have ha : condition n s ≪ probability := cond_absolutelyContinuous
  have he := ha.ae_le (RenewalWallClockResidual.historyResidual_on_event n s hs)
  have hm : ∀ᵐ ω ∂condition n s, ω ∈ event n s := ae_cond_mem (event_measurable n s)
  filter_upwards [he,hm] with ω hω hmem
  exact hω hmem

theorem conditional_joint_law (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (condition n s).map (observation n s) = (history n s).prod base := by
  rw [← Measure.map_congr (observation_ae n s hs), condition, ProbabilityTheory.cond,
    Measure.map_smul _ (RenewalWallClockResidual.historyResidual_measurable n s).aemeasurable]
  change (probability {ω | count s ω = n})⁻¹ •
    (probability.restrict {ω | count s ω = n}).map (RenewalWallClockResidual.historyResidual n s) =
      ((probability {ω | count s ω = n})⁻¹ • RenewalWallClockResidual.historyLaw n s).prod base
  rw [RenewalWallClockResidual.restricted_joint_law n s hs, Measure.prod_smul_left]

theorem conditional_probability (n : ℕ) (s : ℝ) (hp : probability (event n s) ≠ 0) :
    IsProbabilityMeasure (condition n s) := cond_isProbabilityMeasure hp

theorem history_probability (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : probability (event n s) ≠ 0) : IsProbabilityMeasure (history n s) := by
  have : IsProbabilityMeasure (condition n s) := conditional_probability n s hp
  have : IsProbabilityMeasure ((history n s).prod base) := by
    rw [← conditional_joint_law n s hs]
    infer_instance
  have hi : IsProbabilityMeasure (((history n s).prod base).map Prod.fst) := inferInstance
  simpa only [Measure.map_fst_prod, measure_univ, one_smul] using hi

theorem history_law (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (condition n s).map (ConstructedRenewalPoissonLaw.initialSegment n) = history n s := by
  have he := congrArg (fun ν : Measure (FiniteExponentialRenewal.Sample n × ℝ) => ν.map Prod.fst)
    (conditional_joint_law n s hs)
  rw [Measure.map_map measurable_fst (observation_measurable n s),
    Measure.map_fst_prod, measure_univ, one_smul] at he
  exact he

theorem remaining_law (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : probability (event n s) ≠ 0) : (condition n s).map (remaining n s) = base := by
  have : IsProbabilityMeasure (history n s) := history_probability n s hs hp
  have he := congrArg (fun ν : Measure (FiniteExponentialRenewal.Sample n × ℝ) => ν.map Prod.snd)
    (conditional_joint_law n s hs)
  rw [Measure.map_map measurable_snd (observation_measurable n s),
    Measure.map_snd_prod, measure_univ, one_smul] at he
  exact he

theorem history_remaining_independent (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : probability (event n s) ≠ 0) :
    IndepFun (ConstructedRenewalPoissonLaw.initialSegment n) (remaining n s) (condition n s) := by
  have : IsProbabilityMeasure (condition n s) := conditional_probability n s hp
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (ConstructedRenewalPoissonLaw.initialSegment_measurable n).aemeasurable
    (remaining_measurable n s).aemeasurable).mpr
  rw [history_law n s hs, remaining_law n s hs hp]
  exact conditional_joint_law n s hs

theorem event_measure (n : ℕ) (s : ℝ≥0) : probability (event n s) = poissonMeasure s {n} := by
  rw [← ConstructedRenewalPoissonLaw.countLaw_eq_poisson s,
    RootRenewalOperatorBridge.countLaw, Measure.map_apply (count_measurable s)
      (measurableSet_singleton n)]
  rfl

theorem event_ne_zero (n : ℕ) (s : ℝ≥0) (hs : 0 < s) : probability (event n s) ≠ 0 := by
  rw [event_measure, poissonMeasure_singleton]
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  simpa only [poissonMeasure_real_singleton] using poissonMeasure_real_singleton_pos n hs

end OperatorDerivativeRewrite.Foundation.RenewalConditionalResidual
