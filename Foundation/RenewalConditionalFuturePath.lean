import Foundation.RenewalFreshFutureSource

/-! A whole conditional future count-path law for the actual wall-clock renewal process. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.RenewalConditionalFuturePath
open ExponentialHoldingSequence ExponentialNonexplosiveClock ExponentialRenewalCount
open RenewalConditionalResidual RenewalFreshFutureSource ExponentialSourceRegeneration

def futurePath (s : ℝ) (ω : Sample) : CountPath := fun t => count (s+t) ω-count s ω

theorem futurePath_measurable (s : ℝ) : Measurable (futurePath s) := by
  apply measurable_pi_iff.mpr
  intro t
  exact (measurable_of_countable (fun p : ℕ × ℕ => p.1-p.2)).comp
    ((count_measurable (s+t)).prodMk (count_measurable s))

theorem count_shift_eq {ω : Sample} (hω : Good ω) (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hn : count s ω = n) (hf : Good (fresh n s ω)) (t : ℝ) (ht : 0 ≤ t) :
    count (s+t) ω = n+count t (fresh n s ω) := by
  apply (ConstructedRenewalPoissonLaw.count_eq_iff hω _ (add_nonneg hs ht) _).mpr
  have hi := count_interval hf t ht
  constructor
  · cases hk : count t (fresh n s ω) with
    | zero =>
      have hl := ((ConstructedRenewalPoissonLaw.count_eq_iff hω s hs n).mp hn).1
      simp only [Nat.add_zero]
      linarith
    | succ k =>
      have hl := hi.1
      rw [hk, fresh_clock] at hl
      linarith
  · have hu := hi.2
    rw [fresh_clock, show n+(count t (fresh n s ω)+1) = n+count t (fresh n s ω)+1 by omega] at hu
    linarith

theorem futurePath_eq_fresh (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : probability (event n s) ≠ 0) :
    futurePath s =ᵐ[condition n s] countPath ∘ fresh n s := by
  have ha : condition n s ≪ probability := cond_absolutelyContinuous
  have hm : ∀ᵐ ω ∂condition n s, ω ∈ event n s := ae_cond_mem (event_measurable n s)
  filter_upwards [ha.ae_le good_ae,hm,fresh_good_ae n s hs hp] with ω hω hn hf
  funext t
  change count (s+t) ω-count s ω = count t (fresh n s ω)
  rw [count_shift_eq hω n s hs hn hf t t.coe_nonneg, hn]
  omega

theorem futurePath_preserving (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : probability (event n s) ≠ 0) :
    MeasurePreserving (futurePath s) (condition n s) (probability.map countPath) := by
  refine ⟨futurePath_measurable s, ?_⟩
  rw [Measure.map_congr (futurePath_eq_fresh n s hs hp)]
  have hc : MeasurePreserving countPath probability (probability.map countPath) :=
    ⟨countPath_measurable,rfl⟩
  exact (hc.comp (fresh_preserving n s hs hp)).map_eq

theorem past_future_independent (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : probability (event n s) ≠ 0) :
    IndepFun (ConstructedRenewalPoissonLaw.initialSegment n) (futurePath s) (condition n s) := by
  have hi := (past_fresh_independent n s hs hp).comp measurable_id countPath_measurable
  exact hi.congr (Eventually.of_forall (fun _ => rfl)) (futurePath_eq_fresh n s hs hp).symm

theorem past_future_preserving (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : probability (event n s) ≠ 0) :
    MeasurePreserving (fun ω => (ConstructedRenewalPoissonLaw.initialSegment n ω,futurePath s ω))
      (condition n s) ((history n s).prod (probability.map countPath)) := by
  have : IsProbabilityMeasure (condition n s) := conditional_probability n s hp
  refine ⟨(ConstructedRenewalPoissonLaw.initialSegment_measurable n).prodMk
    (futurePath_measurable s), ?_⟩
  rw [(past_future_independent n s hs hp).map_prod_eq_prod_map_map
    (ConstructedRenewalPoissonLaw.initialSegment_measurable n).aemeasurable
    (futurePath_measurable s).aemeasurable,
    history_law n s hs, (futurePath_preserving n s hs hp).map_eq]

end OperatorDerivativeRewrite.Foundation.RenewalConditionalFuturePath
