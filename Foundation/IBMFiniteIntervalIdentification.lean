import Foundation.IBMTerminalPredictableSeries
import Mathlib.Data.Finset.Max

/-! Finite interval-process relations identify actual stochastic sums.
Endpoint charges avoid choosing a new partition or a new process domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFiniteIntervalIdentification
set_option backward.isDefEq.respectTransparency false

theorem tail_relation (S : Finset ℝ≥0) (c w : ℝ≥0 → ℝ) (hw : w 0 = 0)
    (hc : ∀ r ∈ S, 0 < r → (∑ v ∈ S, if r ≤ v then c v else 0) = 0) :
    (∑ v ∈ S, c v * w v) = 0 := by
  classical
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hmax ih =>
    have hn : a ∉ S := fun ha => (hmax a ha).false
    by_cases ha : a = 0
    · subst a
      have he : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
        (fun x hx => (not_lt_of_ge (zero_le : 0 ≤ x)) (hmax x hx))
      simp [he, hw]
    · have hp : 0 < a := pos_iff_ne_zero.mpr ha
      have hz : c a = 0 := by
        have he := hc a (Finset.mem_insert_self a S) hp
        have hs : (∑ v ∈ S, if a ≤ v then c v else 0) = 0 :=
          Finset.sum_eq_zero fun v hv => ite_eq_right (not_le_of_gt (hmax v hv))
        simpa only [Finset.sum_insert hn, le_refl, ite_true, hs, add_zero] using he
      rw [Finset.sum_insert hn, hz, zero_mul, zero_add]
      apply ih
      intro r hr hrpos
      have he := hc r (Finset.mem_insert_of_mem hr) hrpos
      simpa only [Finset.sum_insert hn, hz, ite_self, zero_add] using he

def charge {ι : Type*} (I : Finset ι) (s t : ι → ℝ≥0) (a : ι → ℝ) (v : ℝ≥0) : ℝ :=
  ∑ i ∈ I, ((if t i = v then a i else 0) - (if s i = v then a i else 0))

theorem charge_pairing {ι : Type*} (I : Finset ι) (s t : ι → ℝ≥0) (a : ι → ℝ)
    (S : Finset ℝ≥0) (hs : ∀ i ∈ I, s i ∈ S) (ht : ∀ i ∈ I, t i ∈ S)
    (w : ℝ≥0 → ℝ) :
    (∑ v ∈ S, charge I s t a v * w v) = ∑ i ∈ I, a i * (w (t i) - w (s i)) := by
  classical
  simp only [charge, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, ht i hi, hs i hi, ite_true]
  ring

theorem interval_prefix_difference {s t : ℝ≥0} (hst : s ≤ t) (r : ℝ≥0) (a : ℝ) :
    a * ((if r ≤ t then (1 : ℝ) else 0) - (if r ≤ s then 1 else 0)) =
      (Ioc s t).indicator (fun _ => a) r := by
  by_cases hsr : s < r
  · by_cases hrt : r ≤ t <;>
      simp [Set.indicator, Set.mem_Ioc, hsr, hrt, not_le_of_gt hsr]
  · have hrs := le_of_not_gt hsr
    have hrt := hrs.trans hst
    simp [Set.indicator, Set.mem_Ioc, hsr, hrs, hrt]

theorem interval_relation {ι : Type*} (I : Finset ι) (s t : ι → ℝ≥0) (a : ι → ℝ)
    (hst : ∀ i ∈ I, s i ≤ t i) (x : ℝ≥0 → ℝ)
    (he : ∀ r ∈ I.image s ∪ I.image t,
      (∑ i ∈ I, (Ioc (s i) (t i)).indicator (fun _ => a i) r) = 0) :
    (∑ i ∈ I, a i * (x (t i) - x (s i))) = 0 := by
  classical
  let S := I.image s ∪ I.image t
  have hs (i) (hi : i ∈ I) : s i ∈ S := Finset.mem_union_left _ (Finset.mem_image_of_mem s hi)
  have ht (i) (hi : i ∈ I) : t i ∈ S := Finset.mem_union_right _ (Finset.mem_image_of_mem t hi)
  have hz := tail_relation S (charge I s t a) (fun v => x v - x 0) (sub_self _) (by
    intro r hr _
    calc
      (∑ v ∈ S, if r ≤ v then charge I s t a v else 0) =
          ∑ v ∈ S, charge I s t a v * (if r ≤ v then 1 else 0) := by
            simp only [mul_ite, mul_one, mul_zero]
      _ = ∑ i ∈ I, a i * ((if r ≤ t i then 1 else 0) - (if r ≤ s i then 1 else 0)) :=
        charge_pairing I s t a S hs ht _
      _ = ∑ i ∈ I, (Ioc (s i) (t i)).indicator (fun _ => a i) r :=
        Finset.sum_congr rfl fun i hi => interval_prefix_difference (hst i hi) r (a i)
      _ = 0 := he r hr)
  rw [charge_pairing I s t a S hs ht] at hz
  convert hz using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem interval_relation_ae {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (I : Finset ι) (s t : ι → ℝ≥0) (a : ι → Ω → ℝ)
    (hst : ∀ i ∈ I, s i ≤ t i) (x : ℝ≥0 → Ω → ℝ)
    (he : ∀ r, (fun ω => ∑ i ∈ I, (Ioc (s i) (t i)).indicator (fun _ => a i ω) r)
      =ᵐ[μ] (fun _ => (0 : ℝ))) :
    (fun ω => ∑ i ∈ I, a i ω * (x (t i) ω - x (s i) ω)) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
  classical
  have hh := (Finset.eventually_all (I.image s ∪ I.image t)).mpr (fun r _ => he r)
  filter_upwards [hh] with ω hω
  exact interval_relation I s t (fun i => a i ω) hst (fun r => x r ω) hω

theorem interval_equal_ae {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace Ω]
    (μ : Measure Ω) (s t : ι → ℝ≥0) (a : ι → Ω → ℝ)
    (u v : κ → ℝ≥0) (b : κ → Ω → ℝ) (hst : ∀ i, s i ≤ t i) (huv : ∀ j, u j ≤ v j)
    (x : ℝ≥0 → Ω → ℝ)
    (he : ∀ r, (fun ω => ∑ i, (Ioc (s i) (t i)).indicator (fun _ => a i ω) r)
      =ᵐ[μ] (fun ω => ∑ j, (Ioc (u j) (v j)).indicator (fun _ => b j ω) r)) :
    (fun ω => ∑ i, a i ω * (x (t i) ω - x (s i) ω)) =ᵐ[μ]
      (fun ω => ∑ j, b j ω * (x (v j) ω - x (u j) ω)) := by
  classical
  have h0 := interval_relation_ae μ (Finset.univ : Finset (ι ⊕ κ))
    (Sum.elim s u) (Sum.elim t v) (Sum.elim a (fun j ω => -b j ω))
    (by intro i _; cases i with | inl i => exact hst i | inr j => exact huv j) x (by
      intro r
      filter_upwards [he r] with ω hω
      simpa [Fintype.sum_sum_type, Set.indicator_neg, Finset.sum_neg_distrib, sub_eq_add_neg]
        using sub_eq_zero.mpr hω)
  filter_upwards [h0] with ω hω
  apply sub_eq_zero.mp
  simpa [Fintype.sum_sum_type, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
    using hω

open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction IBMTerminalPredictableStep
open IBMIntrinsicMartingaleStep (Coefficient)

theorem finiteClass_ae {ι : Type*} [Fintype ι] (F : JointL2)
    (s t : ι → ℝ≥0) (a : ∀ i, Coefficient (s i)) :
    (∑ i, stepClass F (s i) (t i) (a i) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      (fun ω => ∑ i, step F (s i) (t i) (a i) ω) := by
  classical
  have hc := (Finset.eventually_all (Finset.univ : Finset ι)).mpr
    (fun i _ => stepClass_ae F (s i) (t i) (a i))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => stepClass F (s i) (t i) (a i)),
    hc] with ω hs ha
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => ha i hi

theorem stochastic_integral_identification {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : JointL2) (s t : ι → ℝ≥0) (a : ∀ i, Coefficient (s i))
    (u v : κ → ℝ≥0) (b : ∀ j, Coefficient (u j))
    (hst : ∀ i, s i ≤ t i) (huv : ∀ j, u j ≤ v j)
    (he : ∀ r, (fun ω => ∑ i, IBMIntrinsicPredictableProcess.timeStep (s i) (t i) (a i) r ω)
      =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => ∑ j, IBMIntrinsicPredictableProcess.timeStep (u j) (v j) (b j) r ω)) :
    (∑ i, stepClass F (s i) (t i) (a i)) = ∑ j, stepClass F (u j) (v j) (b j) := by
  apply Lp.ext
  have hh := interval_equal_ae IBMSourceLaws.jointMeasure s t (fun i => (a i).function)
    u v (fun j => (b j).function) hst huv (IBMRawObservedMartingale.rawValue F) he
  exact (finiteClass_ae F s t a).trans (hh.trans (finiteClass_ae F u v b).symm)

theorem grid_sumClass_identification (F : JointL2) (τ σ : ℕ → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ) (a : ∀ i, Coefficient (τ i))
    (b : ∀ j, Coefficient (σ j)) (n m : ℕ)
    (he : ∀ r, IBMIntrinsicPredictableProcess.timeSum τ a n r
      =ᵐ[IBMSourceLaws.jointMeasure] IBMIntrinsicPredictableProcess.timeSum σ b m r) :
    IBMTerminalPredictableGrid.sumClass F τ a n = IBMTerminalPredictableGrid.sumClass F σ b m := by
  have hh := stochastic_integral_identification F
    (fun i : Fin n => τ i) (fun i : Fin n => τ (i.val + 1)) (fun i : Fin n => a i)
    (fun j : Fin m => σ j) (fun j : Fin m => σ (j.val + 1)) (fun j : Fin m => b j)
    (fun i => hτ (Nat.le_succ i.val)) (fun j => hσ (Nat.le_succ j.val)) (by
      intro r
      filter_upwards [he r] with ω hω
      exact (Fin.sum_univ_eq_sum_range (fun i =>
        IBMIntrinsicPredictableProcess.timeStep (τ i) (τ (i+1)) (a i) r ω) n).trans
          (hω.trans (Fin.sum_univ_eq_sum_range (fun j =>
            IBMIntrinsicPredictableProcess.timeStep (σ j) (σ (j+1)) (b j) r ω) m).symm))
  exact (Fin.sum_univ_eq_sum_range (fun i => stepClass F (τ i) (τ (i+1)) (a i)) n).symm.trans
    (hh.trans (Fin.sum_univ_eq_sum_range (fun j => stepClass F (σ j) (σ (j+1)) (b j)) m))

theorem reversed_interval_counterexample :
    IBMIntrinsicPredictableProcess.timeStep 1 0
      (IBMIntrinsicMartingaleRefinement.constant 1 1) = 0 ∧
    stepClass (IBMDeterministicRangeObstruction.observed 1) 1 0
      (IBMIntrinsicMartingaleRefinement.constant 1 1) ≠ 0 := by
  constructor
  · have he : Ioc (1 : ℝ≥0) 0 = ∅ := Ioc_eq_empty_of_le zero_le
    funext r ω
    simp only [IBMIntrinsicPredictableProcess.timeStep, he, indicator_empty, Pi.zero_apply]
  · rw [IBMTerminalIntegralEnergy.unit_stepClass,
      IBMRawObservedMartingale.raw_origin_class _
        (IBMDeterministicRangeObstruction.observed_centered 1),
      IBMRawObservedMartingale.raw_terminal_class _
        (IBMDeterministicRangeObstruction.observed_mem_past 1) le_rfl, zero_sub]
    exact neg_ne_zero.mpr IBMDeterministicRangeObstruction.observed_one_ne_zero

end OperatorDerivativeRewrite.Foundation.IBMFiniteIntervalIdentification
