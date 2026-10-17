import Foundation.FiniteExponentialRenewal
import Foundation.RootRenewalOperatorBridge

/-! The constructed nonexplosive exponential renewal count has the actual Poisson law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ConstructedRenewalPoissonLaw
open ExponentialHoldingSequence ExponentialNonexplosiveClock ExponentialRenewalCount

def initialSegment (n : ℕ) (ω : Sample) : FiniteExponentialRenewal.Sample n :=
  fun i => holding i.val ω

theorem initialSegment_measurable (n : ℕ) : Measurable (initialSegment n) :=
  measurable_pi_iff.mpr (fun i => holding_measurable i.val)

theorem initialSegment_preserving (n : ℕ) :
    MeasurePreserving (initialSegment n) probability (FiniteExponentialRenewal.probability n) := by
  refine ⟨initialSegment_measurable n, ?_⟩
  change probability.map (fun ω (i : Fin n) => holding i.val ω) = Measure.pi (fun _ : Fin n => base)
  have hi := holding_independent.precomp (g := fun i : Fin n => i.val) Fin.val_injective
  simpa only [holding_law] using
    hi.map_fun_eq_pi_map (fun i : Fin n => (holding_measurable i.val).aemeasurable)

theorem partial_initialSegment (n : ℕ) (ω : Sample) :
    FiniteExponentialRenewal.partialSum n (initialSegment (n+1) ω) = clock n ω := by
  unfold FiniteExponentialRenewal.partialSum initialSegment clock
  simpa only [Fin.val_castSucc] using
    Fin.sum_univ_eq_sum_range (fun i => holding i ω) n

theorem total_initialSegment (n : ℕ) (ω : Sample) :
    FiniteExponentialRenewal.total n (initialSegment (n+1) ω) = clock (n+1) ω := by
  unfold FiniteExponentialRenewal.total initialSegment clock
  exact Fin.sum_univ_eq_sum_range (fun i => holding i ω) (n+1)

theorem count_eq_iff {ω : Sample} (h : Good ω) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    count t ω = n ↔ clock n ω ≤ t ∧ t < clock (n+1) ω := by
  constructor
  · intro hn
    simpa only [hn] using count_interval h t ht
  · intro hn
    have hle : count t ω ≤ n := (ExponentialRenewalSurvival.count_le_iff h t ht n).mpr hn.2
    by_contra hne
    have hlt : count t ω < n := lt_of_le_of_ne hle hne
    have hclock := (good_strictMono h).monotone (Nat.succ_le_iff.mpr hlt)
    have hupper := (count_interval h t ht).2
    linarith [hn.1]

theorem count_singleton (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (RootRenewalOperatorBridge.countLaw t).real {n} = ExponentialRenewalWeights.weight n t := by
  have he : RootRenewalOperatorBridge.countLaw t {n} =
      FiniteExponentialRenewal.probability (n+1) (FiniteExponentialRenewal.event n t) := by
    rw [RootRenewalOperatorBridge.countLaw, Measure.map_apply (count_measurable t)
      (measurableSet_singleton n), ← (initialSegment_preserving (n+1)).map_eq,
      Measure.map_apply (initialSegment_measurable (n+1))
        (FiniteExponentialRenewal.event_measurable n t)]
    apply measure_congr
    filter_upwards [good_ae] with ω hω
    apply propext
    change (count t ω = n) ↔ _
    rw [count_eq_iff hω t ht n]
    change _ ↔ FiniteExponentialRenewal.partialSum n (initialSegment (n+1) ω) ≤ t ∧
      t < FiniteExponentialRenewal.total n (initialSegment (n+1) ω)
    rw [partial_initialSegment, total_initialSegment]
  exact (congrArg ENNReal.toReal he).trans (FiniteExponentialRenewal.event_probability n t)

theorem countLaw_eq_poisson (t : ℝ≥0) :
    RootRenewalOperatorBridge.countLaw t = poissonMeasure t := by
  apply Measure.ext_of_singleton
  intro n
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact (count_singleton t t.coe_nonneg n).trans (by
    change ExponentialRenewalWeights.weight n t = (poissonMeasure t).real {n}
    rw [poissonMeasure_real_singleton]
    simp [ExponentialRenewalWeights.weight, t.coe_nonneg])

theorem transition_eq_poisson (a : ℝ) (t : ℝ≥0) :
    RootRenewalOperatorBridge.transition a t = ComplexRootPoissonSemigroup.transition a t :=
  RootRenewalOperatorBridge.transition_eq_poisson_of_countLaw a t t (countLaw_eq_poisson t)

theorem process_law_eq_poisson (a : ℝ) (t : ℝ≥0) :
    MarkedRootRenewalProcess.probability.map (MarkedRootRenewalProcess.process a t) =
      ComplexRootPoissonLaw.law t a :=
  RootRenewalOperatorBridge.process_law_eq_poisson_of_countLaw a t t (countLaw_eq_poisson t)

theorem transition_eq_poisson_real (a t : ℝ) (ht : 0 ≤ t) :
    RootRenewalOperatorBridge.transition a t = ComplexRootPoissonSemigroup.transition a t :=
  transition_eq_poisson a ⟨t,ht⟩

theorem transition_add (a : ℝ) (s t : ℝ≥0) :
    RootRenewalOperatorBridge.transition a (s+t : ℝ≥0) =
      (RootRenewalOperatorBridge.transition a s).comp
        (RootRenewalOperatorBridge.transition a t) := by
  rw [transition_eq_poisson, transition_eq_poisson, transition_eq_poisson, NNReal.coe_add]
  exact ComplexRootPoissonSemigroup.transition_add a s t

theorem transition_hasDerivAt (a t : ℝ) (ht : 0 < t) :
    HasDerivAt (RootRenewalOperatorBridge.transition a)
      ((RootRenewalOperatorBridge.transition a t).comp
        (ComplexRootTransitionOperator.step a -
          ContinuousLinearMap.id ℂ ComplexRootTransitionOperator.Test))
      t := by
  have he : RootRenewalOperatorBridge.transition a =ᶠ[𝓝 t]
      ComplexRootPoissonSemigroup.transition a := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact transition_eq_poisson_real a u (le_of_lt hu)
  have hd := ComplexRootPoissonSemigroup.transition_hasDerivAt a t
  rw [← transition_eq_poisson_real a t ht.le] at hd
  exact hd.congr_of_eventuallyEq he

end OperatorDerivativeRewrite.Foundation.ConstructedRenewalPoissonLaw
