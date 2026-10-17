import Foundation.RenewalConditionalFuturePath

/-! Reconstruct the actual entire observed count past from its completed holding prefix. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.RenewalPastReconstruction
open ExponentialHoldingSequence ExponentialNonexplosiveClock ExponentialRenewalCount
open RenewalConditionalResidual RenewalConditionalFuturePath

def arrival (n k : ℕ) (ξ : FiniteExponentialRenewal.Sample n) : ℝ :=
  ∑ i ∈ Finset.range k, if h : i < n then ξ ⟨i,h⟩ else 0

theorem arrival_measurable (n k : ℕ) : Measurable (arrival n k) := by
  classical
  unfold arrival
  apply Finset.measurable_sum
  intro i hi
  split_ifs <;> fun_prop

theorem arrival_initialSegment (n k : ℕ) (hk : k ≤ n) (ω : Sample) :
    arrival n k (ConstructedRenewalPoissonLaw.initialSegment n ω) = clock k ω := by
  unfold arrival clock
  apply Finset.sum_congr rfl
  intro i hi
  rw [dite_eq_left (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)]
  rfl

def pastCount (n : ℕ) (u : ℝ) (ξ : FiniteExponentialRenewal.Sample n) : ℕ :=
  ∑ j ∈ Finset.range n, if arrival n (j+1) ξ ≤ u then 1 else 0

theorem pastCount_measurable (n : ℕ) (u : ℝ) : Measurable (pastCount n u) := by
  classical
  unfold pastCount
  apply Finset.measurable_sum
  intro j hj
  exact Measurable.ite (measurableSet_le (arrival_measurable n (j+1)) measurable_const)
    measurable_const measurable_const

theorem pastCount_eq {ω : Sample} (hω : Good ω) (n : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hn : count u ω ≤ n) :
    pastCount n u (ConstructedRenewalPoissonLaw.initialSegment n ω) = count u ω := by
  classical
  have hc (j : ℕ) : clock (j+1) ω ≤ u ↔ j < count u ω := by
    simpa only [not_le, not_lt] using
      (not_congr (ExponentialRenewalSurvival.count_le_iff hω u hu j)).symm
  have he : (Finset.range n).filter (fun j => j < count u ω) = Finset.range (count u ω) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    exact and_iff_right_of_imp (fun hj => lt_of_lt_of_le hj hn)
  calc
    _ = ∑ j ∈ Finset.range n, if j < count u ω then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [arrival_initialSegment n (j+1)
        (Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)), hc j]
    _ = count u ω := by rw [← Finset.sum_filter, he]; simp

abbrev PastPath (s : ℝ≥0) := Set.Iic s → ℕ
def pastPath (s : ℝ≥0) (ω : Sample) : PastPath s := fun u => count u ω
def reconstruct (n : ℕ) (s : ℝ≥0) (ξ : FiniteExponentialRenewal.Sample n) : PastPath s :=
  fun u => pastCount n u ξ

theorem pastPath_measurable (s : ℝ≥0) : Measurable (pastPath s) :=
  measurable_pi_iff.mpr (fun u => count_measurable u)

theorem reconstruct_measurable (n : ℕ) (s : ℝ≥0) : Measurable (reconstruct n s) :=
  measurable_pi_iff.mpr (fun u => pastCount_measurable n u)

theorem pastPath_eq_reconstruct (n : ℕ) (s : ℝ≥0) :
    pastPath s =ᵐ[condition n s]
      reconstruct n s ∘ ConstructedRenewalPoissonLaw.initialSegment n := by
  have ha : condition n s ≪ probability := cond_absolutelyContinuous
  have hm : ∀ᵐ ω ∂condition n s, ω ∈ event n s := ae_cond_mem (event_measurable n s)
  filter_upwards [ha.ae_le good_ae,hm] with ω hω hn
  funext u
  exact (pastCount_eq hω n u u.1.coe_nonneg
    (calc count u ω ≤ count s ω := count_monotone ω (show (u : ℝ) ≤ s from u.2)
          _ = n := hn)).symm

theorem conditional_past_future_independent (n : ℕ) (s : ℝ≥0)
    (hp : probability (event n s) ≠ 0) :
    IndepFun (pastPath s) (futurePath s) (condition n s) := by
  have hi := (past_future_independent n s s.coe_nonneg hp).comp
    (reconstruct_measurable n s) measurable_id
  exact hi.congr (pastPath_eq_reconstruct n s).symm (Eventually.of_forall (fun _ => rfl))

end OperatorDerivativeRewrite.Foundation.RenewalPastReconstruction
