import Foundation.MarkedRealizationRegeneration
import Foundation.RenewalPastReconstruction

/-! Reconstruct actual marked past paths without choosing an artificial default mark. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedRealizationPast
open MarkedRenewalRealization FiniteMarkedRenewalMarginals MarkedConditionalRealization
open ExponentialNonexplosiveClock ExponentialRenewalCount
variable {A : Type*} [MeasurableSpace A]

def prefixPosition (z : A → ℂ) (n k : ℕ) (ξ : Prefix A n) : ℂ :=
  ∑ i : Fin n, if i.val < k then z (ξ i) else 0

theorem prefixPosition_joint_measurable (z : A → ℂ) (hz : Measurable z) (n : ℕ) :
    Measurable (fun p : ℕ × Prefix A n => prefixPosition z n p.1 p.2) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    (hz.comp ((measurable_pi_apply i).comp measurable_snd)) measurable_const

theorem prefixPosition_eq (z : A → ℂ) (n k : ℕ) (hk : k ≤ n) (η : MarkSample A) :
    prefixPosition z n k (initialSegment n η) = position z k η := by
  change (∑ i : Fin n, (fun j : ℕ => if j < k then z (η j) else 0) i.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < k then z (η j) else 0) n]
  have he : (∑ j ∈ Finset.range k, if j < k then z (η j) else 0) =
      ∑ j ∈ Finset.range n, if j < k then z (η j) else 0 :=
    Finset.sum_subset (Finset.range_mono hk) (fun j _ hj => by
      rw [ite_eq_right (by simpa only [Finset.mem_range] using hj)])
  rw [← he]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_left (Finset.mem_range.mp hj)]

abbrev PastPath (s : ℝ≥0) := Set.Iic s → ℂ

def pastPath (z : A → ℂ) (s : ℝ≥0) (ω : Sample A) : PastPath s := fun u => process z u ω

def reconstruct (z : A → ℂ) (n : ℕ) (s : ℝ≥0) (p : PastState A n) : PastPath s :=
  fun u => prefixPosition z n (RenewalPastReconstruction.pastCount n u p.1) p.2

theorem pastPath_measurable (z : A → ℂ) (hz : Measurable z) (s : ℝ≥0) :
    Measurable (pastPath z s) := measurable_pi_iff.mpr (fun u => process_measurable z hz u)

theorem reconstruct_measurable (z : A → ℂ) (hz : Measurable z) (n : ℕ) (s : ℝ≥0) :
    Measurable (reconstruct z n s) := by
  apply measurable_pi_iff.mpr
  intro u
  have hc : Measurable (fun p : PastState A n => RenewalPastReconstruction.pastCount n u p.1) :=
    (RenewalPastReconstruction.pastCount_measurable n u).comp measurable_fst
  exact (prefixPosition_joint_measurable z hz n).comp (hc.prodMk measurable_snd)

theorem pastPath_eq_reconstruct (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (n : ℕ) (s : ℝ≥0) :
    pastPath z s =ᵐ[condition μ n s] reconstruct z n s ∘ past n := by
  have ha : condition μ n s ≪ probability μ := cond_absolutelyContinuous
  have hm : ∀ᵐ ω ∂condition μ n s, ω ∈ event n s := ae_cond_mem (event_measurable n s)
  filter_upwards [ha.ae_le (clock_good_ae μ),hm] with ω hω hn
  funext u
  have hle : count u ω.1 ≤ n := calc
    count u ω.1 ≤ count s ω.1 := count_monotone ω.1 (show (u : ℝ) ≤ s from u.2)
    _ = n := hn
  have hc := RenewalPastReconstruction.pastCount_eq hω n u u.1.coe_nonneg hle
  change position z (count u ω.1) ω.2 =
    prefixPosition z n (RenewalPastReconstruction.pastCount n u
      (ConstructedRenewalPoissonLaw.initialSegment n ω.1)) (initialSegment n ω.2)
  rw [hc,prefixPosition_eq z n _ hle]

theorem conditional_past_future_independent (μ : Measure A) [IsProbabilityMeasure μ]
    (z : A → ℂ) (hz : Measurable z) (n : ℕ) (s : ℝ≥0)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    IndepFun (pastPath z s) (MarkedRealizationRegeneration.futurePath z s) (condition μ n s) := by
  have hi := (MarkedRealizationRegeneration.past_future_independent μ z hz n s s.coe_nonneg hp).comp
    (reconstruct_measurable z hz n s) measurable_id
  exact hi.congr (pastPath_eq_reconstruct μ z n s).symm (Eventually.of_forall (fun _ => rfl))

end OperatorDerivativeRewrite.Foundation.MarkedRealizationPast
