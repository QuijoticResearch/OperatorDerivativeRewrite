import Foundation.ExponentialRenewalWeights
import Foundation.ExponentialRenewalSurvival
import Mathlib.MeasureTheory.Integral.Prod

/-! Finite exponential cylinder events and their actual renewal probabilities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace OperatorDerivativeRewrite.Foundation.FiniteExponentialRenewal

abbrev Sample (n : ℕ) := Fin n → ℝ
def probability (n : ℕ) : Measure (Sample n) :=
  Measure.pi (fun _ => ExponentialHoldingSequence.base)
instance probability_isProbability (n : ℕ) : IsProbabilityMeasure (probability n) := by
  unfold probability
  infer_instance

def partialSum (n : ℕ) (ω : Sample (n + 1)) : ℝ := ∑ i : Fin n, ω i.castSucc
def total (n : ℕ) (ω : Sample (n + 1)) : ℝ := ∑ i, ω i
def event (n : ℕ) (t : ℝ) : Set (Sample (n + 1)) :=
  {ω | partialSum n ω ≤ t ∧ t < total n ω}
def observable (n : ℕ) (t : ℝ) : Sample (n + 1) → ℝ := (event n t).indicator 1
def mass (n : ℕ) (t : ℝ) : ℝ := ∫ ω, observable n t ω ∂probability (n + 1)

theorem event_measurable (n : ℕ) (t : ℝ) : MeasurableSet (event n t) := by
  have hp : Measurable (partialSum n) := by unfold partialSum; fun_prop
  have hq : Measurable (total n) := by unfold total; fun_prop
  have hleft : MeasurableSet {ω | partialSum n ω ≤ t} := measurableSet_le hp measurable_const
  have hright : MeasurableSet {ω | t < total n ω} := measurableSet_lt measurable_const hq
  exact hleft.inter hright

theorem observable_joint_measurable (n : ℕ) :
    Measurable (fun p : ℝ × Sample (n + 1) => observable n p.1 p.2) := by
  unfold observable event partialSum total
  apply measurable_const.indicator
  exact (measurableSet_le (by fun_prop) measurable_fst).inter
    (measurableSet_lt measurable_fst (by fun_prop))

theorem observable_bound (n : ℕ) (t : ℝ) (ω : Sample (n + 1)) :
    ‖observable n t ω‖ ≤ 1 := by
  unfold observable
  by_cases h : ω ∈ event n t <;> simp [h]

theorem observable_integrable (n : ℕ) (t : ℝ) :
    Integrable (observable n t) (probability (n + 1)) := by
  apply Integrable.of_bound
    ((observable_joint_measurable n).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
  exact Eventually.of_forall (observable_bound n t)

theorem partial_cons (n : ℕ) (s : ℝ) (ω : Sample (n + 1)) :
    partialSum (n + 1) (Fin.cons s ω) = s + partialSum n ω := by
  simp [partialSum, Fin.sum_univ_succ]

theorem total_cons (n : ℕ) (s : ℝ) (ω : Sample (n + 1)) :
    total (n + 1) (Fin.cons s ω) = s + total n ω := by
  simp [total, Fin.sum_univ_succ]

theorem observable_cons (n : ℕ) (t s : ℝ) (ω : Sample (n + 1)) :
    observable (n + 1) t (Fin.cons s ω) = observable n (t-s) ω := by
  classical
  have he : Fin.cons s ω ∈ event (n + 1) t ↔ ω ∈ event n (t-s) := by
    change partialSum (n + 1) (Fin.cons s ω) ≤ t ∧ t < total (n + 1) (Fin.cons s ω) ↔ _
    rw [partial_cons, total_cons]
    change _ ↔ partialSum n ω ≤ t-s ∧ t-s < total n ω
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  by_cases h : ω ∈ event n (t-s)
  · rw [observable, indicator_of_mem (he.mpr h), observable, indicator_of_mem h]
    rfl
  · rw [observable, indicator_of_notMem (fun hp => h (he.mp hp)), observable,
      indicator_of_notMem h]

theorem mass_succ (n : ℕ) (t : ℝ) :
    mass (n + 1) t = ∫ s, mass n (t-s) ∂ExponentialHoldingSequence.base := by
  unfold mass
  have hm : Measurable (fun p : ℝ × Sample (n + 1) => observable n (t-p.1) p.2) :=
    (observable_joint_measurable n).comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd)
  have hi : Integrable (fun p : ℝ × Sample (n + 1) => observable n (t-p.1) p.2)
      (ExponentialHoldingSequence.base.prod (probability (n + 1))) :=
    Integrable.of_bound hm.aestronglyMeasurable 1
      (Eventually.of_forall (fun p => observable_bound n (t-p.1) p.2))
  calc
    _ = ∫ p : ℝ × Sample (n + 1), observable n (t-p.1) p.2
        ∂ExponentialHoldingSequence.base.prod (probability (n + 1)) := by
      unfold probability
      rw [← ((measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 2) => ExponentialHoldingSequence.base) 0).symm).integral_comp']
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.zero_succAbove, Fin.insertNth_zero, cast_eq]
          using observable_cons n t p.1 p.2)
    _ = _ := integral_prod _ hi

theorem mass_zero (t : ℝ) : mass 0 t = ExponentialRenewalWeights.weight 0 t := by
  classical
  by_cases ht : 0 ≤ t
  · have he : observable 0 t = fun ω : Sample 1 => (Ioi t).indicator (1 : ℝ → ℝ) (ω 0) := by
      funext ω
      by_cases h : t < ω 0
      · have hmem : ω ∈ event 0 t := by simp [event, partialSum, total, ht, h]
        simp [observable, indicator_of_mem hmem, h]
      · have hmem : ω ∉ event 0 t := by simp [event, partialSum, total, ht, h]
        simp [observable, indicator_of_notMem hmem, h]
    rw [mass, he, probability,
      integral_comp_eval (μ := fun _ : Fin 1 => ExponentialHoldingSequence.base)
        (i := 0) (f := (Ioi t).indicator (1 : ℝ → ℝ))
        (measurable_const.indicator measurableSet_Ioi).aestronglyMeasurable,
      integral_indicator_one measurableSet_Ioi, ExponentialRenewalSurvival.base_survival t ht]
    simp [ExponentialRenewalWeights.weight, ht]
  · simp [mass, observable, event, partialSum, ht, ExponentialRenewalWeights.weight]

theorem mass_eq_weight (n : ℕ) (t : ℝ) : mass n t = ExponentialRenewalWeights.weight n t := by
  induction n generalizing t with
  | zero => exact mass_zero t
  | succ n ih =>
    rw [mass_succ]
    simp_rw [ih]
    exact ExponentialRenewalWeights.weight_convolution n t

theorem event_probability (n : ℕ) (t : ℝ) :
    (probability (n + 1)).real (event n t) = ExponentialRenewalWeights.weight n t := by
  rw [← integral_indicator_one (event_measurable n t)]
  exact mass_eq_weight n t

end OperatorDerivativeRewrite.Foundation.FiniteExponentialRenewal
