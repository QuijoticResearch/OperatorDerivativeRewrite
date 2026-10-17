import Foundation.RenewalConditionalTail

/-! An actual fresh exponential sequence reconstructed at a deterministic observation time. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace OperatorDerivativeRewrite.Foundation.RenewalFreshFutureSource
open ExponentialHoldingSequence ExponentialNonexplosiveClock ExponentialRenewalCount
open RenewalConditionalResidual ExponentialSourceRegeneration

def prepend (p : ℝ × Sample) : Sample := fun j => Nat.casesOn j p.1 (fun k => p.2 k)

theorem prepend_measurable : Measurable prepend := by
  apply measurable_pi_iff.mpr
  intro j
  cases j with
  | zero => exact measurable_fst
  | succ j => exact (measurable_pi_apply j).comp measurable_snd

theorem head_tail_law :
    probability.map (fun ω => (holding 0 ω,tail 1 ω)) = base.prod probability := by
  have hi : IndepFun (holding 0) (tail 1) probability := by
    have he := (past_tail_independent 1).comp (measurable_pi_apply (0 : Fin 1)) measurable_id
    simpa only [ConstructedRenewalPoissonLaw.initialSegment, Function.comp_def, id_eq,
      Fin.val_zero] using he
  rw [hi.map_prod_eq_prod_map_map (holding_measurable 0).aemeasurable
    (tail_measurable 1).aemeasurable, holding_law, (tail_preserving 1).map_eq]

theorem prepend_head_tail (ω : Sample) : prepend (holding 0 ω,tail 1 ω) = ω := by
  funext j
  cases j with
  | zero => rfl
  | succ j => simp [prepend, tail, holding, Nat.add_comm]

theorem prepend_preserving : MeasurePreserving prepend (base.prod probability) probability := by
  refine ⟨prepend_measurable, ?_⟩
  have he := Measure.map_map prepend_measurable
    ((holding_measurable 0).prodMk (tail_measurable 1)) (μ := probability)
  rw [head_tail_law, show (prepend ∘ fun ω => (holding 0 ω,tail 1 ω)) = id from
    funext prepend_head_tail, Measure.map_id] at he
  exact he

def fresh (n : ℕ) (s : ℝ) (ω : Sample) : Sample := prepend (remaining n s ω,tail (n+1) ω)

theorem fresh_measurable (n : ℕ) (s : ℝ) : Measurable (fresh n s) :=
  prepend_measurable.comp ((remaining_measurable n s).prodMk (tail_measurable (n+1)))

theorem past_fresh_preserving (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : probability (event n s) ≠ 0) :
    MeasurePreserving (fun ω => (ConstructedRenewalPoissonLaw.initialSegment n ω,fresh n s ω))
      (condition n s) ((history n s).prod probability) := by
  have : IsProbabilityMeasure (history n s) := history_probability n s hs hp
  have hobs : MeasurePreserving (fun ω => (observation n s ω,tail (n+1) ω))
      (condition n s) (((history n s).prod base).prod probability) :=
    ⟨(observation_measurable n s).prodMk (tail_measurable (n+1)),
      RenewalConditionalTail.observation_tail_law n s hs hp⟩
  have he := (((MeasurePreserving.id (history n s)).prod prepend_preserving).comp
    (measurePreserving_prodAssoc (history n s) base probability)).comp hobs
  exact he

theorem fresh_preserving (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : probability (event n s) ≠ 0) :
    MeasurePreserving (fresh n s) (condition n s) probability := by
  have : IsProbabilityMeasure (history n s) := history_probability n s hs hp
  exact measurePreserving_snd.comp (past_fresh_preserving n s hs hp)

theorem past_fresh_independent (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hp : probability (event n s) ≠ 0) :
    IndepFun (ConstructedRenewalPoissonLaw.initialSegment n) (fresh n s) (condition n s) := by
  have : IsProbabilityMeasure (condition n s) := conditional_probability n s hp
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (ConstructedRenewalPoissonLaw.initialSegment_measurable n).aemeasurable
    (fresh_measurable n s).aemeasurable).mpr
  rw [history_law n s hs, (fresh_preserving n s hs hp).map_eq]
  exact (past_fresh_preserving n s hs hp).map_eq

theorem fresh_good_ae (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (hp : probability (event n s) ≠ 0) :
    ∀ᵐ ω ∂condition n s, Good (fresh n s ω) :=
  (fresh_preserving n s hs hp).quasiMeasurePreserving.ae good_ae

theorem clock_prepend (m : ℕ) (h : ℝ) (η : Sample) :
    clock (m+1) (prepend (h,η)) = h + clock m η := by
  simp [clock, Finset.sum_range_succ', prepend, holding, add_comm]

theorem fresh_clock (n m : ℕ) (s : ℝ) (ω : Sample) :
    clock (m+1) (fresh n s ω) = clock (n+(m+1)) ω-s := by
  rw [fresh, clock_prepend, remaining]
  have he := clock_add (n+1) m ω
  rw [show n+(m+1) = (n+1)+m by omega, he]
  ring

end OperatorDerivativeRewrite.Foundation.RenewalFreshFutureSource
