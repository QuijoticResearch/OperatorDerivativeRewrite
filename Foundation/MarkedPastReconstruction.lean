import Foundation.MarkedRenewalRegeneration
import Foundation.RenewalPastReconstruction

/-! Reconstruct the entire observed complex past from completed holding and mark prefixes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedPastReconstruction
open MarkedRootRenewalProcess MarkedConditionalSource
open ExponentialNonexplosiveClock ExponentialRenewalCount

def extend (n : ℕ) (ξ : ComplexFourthRootWalk.Sample n) : MarkSample :=
  fun j => if h : j < n then ξ ⟨j,h⟩ else 0

theorem extend_measurable (n : ℕ) : Measurable (extend n) := by
  classical
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : j < n
  · simpa only [extend, dite_eq_left h] using
      (measurable_pi_apply (⟨j,h⟩ : Fin n) :
        Measurable (fun ξ : ComplexFourthRootWalk.Sample n => ξ ⟨j,h⟩))
  · simp only [extend, dite_eq_right h]
    exact measurable_const

theorem position_extend (a : ℝ) (n k : ℕ) (hk : k ≤ n) (η : MarkSample) :
    position a k (extend n (RootRenewalWalkMarginal.initialSegment n η)) = position a k η := by
  unfold position
  apply Finset.sum_congr rfl
  intro j hj
  have h : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj) hk
  simp only [extend, dite_eq_left h, RootRenewalWalkMarginal.initialSegment]

abbrev PastPath (s : ℝ≥0) := Set.Iic s → ℂ
def pastPath (a : ℝ) (s : ℝ≥0) (ω : StateSample) : PastPath s := fun u => process a u ω
def reconstruct (a : ℝ) (n : ℕ) (s : ℝ≥0) (p : PastState n) : PastPath s :=
  fun u => position a (RenewalPastReconstruction.pastCount n u p.1) (extend n p.2)

theorem pastPath_measurable (a : ℝ) (s : ℝ≥0) : Measurable (pastPath a s) :=
  measurable_pi_iff.mpr (fun u => process_measurable a u)

theorem reconstruct_measurable (a : ℝ) (n : ℕ) (s : ℝ≥0) : Measurable (reconstruct a n s) := by
  apply measurable_pi_iff.mpr
  intro u
  have hc : Measurable (fun p : PastState n => RenewalPastReconstruction.pastCount n u p.1) :=
    (RenewalPastReconstruction.pastCount_measurable n u).comp measurable_fst
  have hm : Measurable (fun p : PastState n => extend n p.2) :=
    (extend_measurable n).comp measurable_snd
  have he := (position_joint_measurable a).comp (hc.prodMk hm)
  simpa only [Function.comp_def, reconstruct] using he

theorem pastPath_eq_reconstruct (a : ℝ) (n : ℕ) (s : ℝ≥0) :
    pastPath a s =ᵐ[condition n s] reconstruct a n s ∘ past n := by
  have ha : condition n s ≪ probability := cond_absolutelyContinuous
  have hm : ∀ᵐ ω ∂condition n s, ω ∈ event n s := ae_cond_mem (event_measurable n s)
  filter_upwards [ha.ae_le clock_good_ae,hm] with ω hω hn
  funext u
  have hle : count u ω.1 ≤ n := calc
    count u ω.1 ≤ count s ω.1 := count_monotone ω.1 (show (u : ℝ) ≤ s from u.2)
    _ = n := hn
  have hc := RenewalPastReconstruction.pastCount_eq hω n u u.1.coe_nonneg hle
  change position a (count u ω.1) ω.2 =
    position a (RenewalPastReconstruction.pastCount n u
      (ConstructedRenewalPoissonLaw.initialSegment n ω.1))
      (extend n (RootRenewalWalkMarginal.initialSegment n ω.2))
  rw [hc,position_extend a n _ hle]

theorem conditional_past_future_independent (a : ℝ) (n : ℕ) (s : ℝ≥0)
    (hp : ExponentialHoldingSequence.probability (RenewalConditionalResidual.event n s) ≠ 0) :
    IndepFun (pastPath a s) (MarkedRenewalRegeneration.futurePath a s) (condition n s) := by
  have hi := (MarkedRenewalRegeneration.past_future_independent a n s s.coe_nonneg hp).comp
    (reconstruct_measurable a n s) measurable_id
  exact hi.congr (pastPath_eq_reconstruct a n s).symm (Eventually.of_forall (fun _ => rfl))

end OperatorDerivativeRewrite.Foundation.MarkedPastReconstruction
