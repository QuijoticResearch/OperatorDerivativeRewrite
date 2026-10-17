import Foundation.ExponentialNonexplosiveClock

/-! A jointly measurable, finite renewal count built from the actual exponential clock. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ExponentialRenewalCount
open ExponentialHoldingSequence ExponentialNonexplosiveClock

def Crossed (t : ℝ) (ω : Sample) (n : ℕ) : Prop :=
  (Good ω ∧ t < clock n ω) ∨ (¬ Good ω ∧ n = 0)

theorem exists_crossed (t : ℝ) (ω : Sample) : ∃ n, Crossed t ω n := by
  by_cases h : Good ω
  · obtain ⟨n,hn⟩ := good_exists_above h t
    exact ⟨n,Or.inl ⟨h,hn⟩⟩
  · exact ⟨0,Or.inr ⟨h,rfl⟩⟩

def firstAbove (t : ℝ) (ω : Sample) : ℕ := by
  classical
  exact Nat.find (exists_crossed t ω)

theorem crossed_measurable (n : ℕ) :
    MeasurableSet {p : ℝ × Sample | Crossed p.1 p.2 n} := by
  have hg : MeasurableSet {p : ℝ × Sample | Good p.2} :=
    good_measurable.preimage measurable_snd
  have ht : MeasurableSet {p : ℝ × Sample | p.1 < clock n p.2} :=
    measurableSet_lt measurable_fst ((clock_measurable n).comp measurable_snd)
  have hn : MeasurableSet {p : ℝ × Sample | n = 0} := by
    by_cases h : n = 0 <;> simp [h]
  exact (hg.inter ht).union (hg.compl.inter hn)

theorem firstAbove_joint_measurable : Measurable (fun p : ℝ × Sample => firstAbove p.1 p.2) := by
  classical
  exact measurable_find (fun p : ℝ × Sample => exists_crossed p.1 p.2) crossed_measurable

theorem firstAbove_spec (t : ℝ) (ω : Sample) : Crossed t ω (firstAbove t ω) := by
  classical
  exact Nat.find_spec (exists_crossed t ω)

theorem firstAbove_above {ω : Sample} (h : Good ω) (t : ℝ) : t < clock (firstAbove t ω) ω :=
  (firstAbove_spec t ω).elim (fun hp => hp.2) (fun hp => False.elim (hp.1 h))

theorem firstAbove_le {ω : Sample} (h : Good ω) (t : ℝ) (n : ℕ) (hn : t < clock n ω) :
    firstAbove t ω ≤ n := by
  classical
  exact Nat.find_min' (exists_crossed t ω) (Or.inl ⟨h,hn⟩)

theorem firstAbove_bad {ω : Sample} (h : ¬ Good ω) (t : ℝ) : firstAbove t ω = 0 := by
  classical
  apply Nat.le_zero.mp
  exact Nat.find_min' (exists_crossed t ω) (Or.inr ⟨h,rfl⟩)

def count (t : ℝ) (ω : Sample) : ℕ := firstAbove t ω-1

theorem count_joint_measurable : Measurable (fun p : ℝ × Sample => count p.1 p.2) :=
  (measurable_of_countable (fun n : ℕ => n-1)).comp firstAbove_joint_measurable

theorem count_measurable (t : ℝ) : Measurable (count t) :=
  count_joint_measurable.comp (measurable_const.prodMk measurable_id)

theorem count_bad {ω : Sample} (h : ¬ Good ω) (t : ℝ) : count t ω = 0 := by
  simp only [count, firstAbove_bad h, Nat.zero_sub]

theorem firstAbove_positive {ω : Sample} (h : Good ω) (t : ℝ) (ht : 0 ≤ t) :
    0 < firstAbove t ω := by
  apply Nat.pos_of_ne_zero
  intro hz
  have he := firstAbove_above h t
  rw [hz, clock_zero] at he
  linarith

theorem count_successor {ω : Sample} (h : Good ω) (t : ℝ) (ht : 0 ≤ t) :
    count t ω+1 = firstAbove t ω :=
  Nat.sub_add_cancel (Nat.succ_le_iff.mpr (firstAbove_positive h t ht))

theorem count_interval {ω : Sample} (h : Good ω) (t : ℝ) (ht : 0 ≤ t) :
    clock (count t ω) ω ≤ t ∧ t < clock (count t ω+1) ω := by
  classical
  constructor
  · apply le_of_not_gt
    intro hx
    have he := Nat.find_min (exists_crossed t ω)
      (show count t ω < firstAbove t ω by
        have hp := firstAbove_positive h t ht
        dsimp [count]
        omega)
    exact he (Or.inl ⟨h,hx⟩)
  · rw [count_successor h t ht]
    exact firstAbove_above h t

theorem count_monotone (ω : Sample) : Monotone (fun t => count t ω) := by
  intro s t hst
  by_cases h : Good ω
  · apply Nat.sub_le_sub_right
    exact firstAbove_le h s _ (lt_of_le_of_lt hst (firstAbove_above h t))
  · simp [count_bad h]

theorem count_zero (ω : Sample) : count 0 ω = 0 := by
  by_cases h : Good ω
  · have hpos := firstAbove_positive h 0 le_rfl
    have hle : firstAbove 0 ω ≤ 1 := firstAbove_le h 0 1 (by
      rw [clock_successor, clock_zero, zero_add]
      exact h.1 0)
    have he : firstAbove 0 ω = 1 := by omega
    simp only [count, he, Nat.sub_self]
  · exact count_bad h 0

theorem count_at_clock {ω : Sample} (h : Good ω) (n : ℕ) : count (clock n ω) ω = n := by
  have hm := good_strictMono h
  have hle : firstAbove (clock n ω) ω ≤ n+1 :=
    firstAbove_le h _ _ (hm (Nat.lt_succ_self n))
  have hlt : n < firstAbove (clock n ω) ω := hm.lt_iff_lt.mp (firstAbove_above h _)
  have he : firstAbove (clock n ω) ω = n+1 := by omega
  simp only [count, he, Nat.add_sub_cancel]

end OperatorDerivativeRewrite.Foundation.ExponentialRenewalCount
