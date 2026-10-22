import Foundation.IBMPredictableRingContent

/-! Compact time fibers with measurably constructed sample projections. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompactPredictableFibers
open IBMPredictableRectangles
set_option backward.isDefEq.respectTransparency false

def compactRectangles : Set (Set Space) :=
  {E | ∃ C : Set ℝ≥0, ∃ A : Set IBMSourceLaws.JointSample,
    IsCompact C ∧ MeasurableSet A ∧ E = C ×ˢ A}

def compactFinite : Set (Set Space) := supClosure compactRectangles

def fiber (E : Set Space) (ω : IBMSourceLaws.JointSample) : Set ℝ≥0 := {r | (r,ω) ∈ E}

def projection (E : Set Space) : Set IBMSourceLaws.JointSample := {ω | (fiber E ω).Nonempty}

theorem compact_empty : (∅ : Set Space) ∈ compactFinite := by
  apply subset_supClosure
  refine ⟨∅, ∅, isCompact_empty, MeasurableSet.empty, ?_⟩
  simp only [empty_prod]

theorem compact_rectangle (C : Set ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hC : IsCompact C) (hA : MeasurableSet A) : C ×ˢ A ∈ compactFinite :=
  subset_supClosure ⟨C, A, hC, hA, rfl⟩

theorem compact_union {E H : Set Space} (hE : E ∈ compactFinite) (hH : H ∈ compactFinite) :
    E ∪ H ∈ compactFinite := supClosed_supClosure hE hH

theorem base_inter {E H : Set Space} (hE : E ∈ compactRectangles) (hH : H ∈ compactRectangles) :
    E ∩ H ∈ compactRectangles := by
  obtain ⟨C, A, hC, hA, rfl⟩ := hE
  obtain ⟨D, B, hD, hB, rfl⟩ := hH
  refine ⟨C ∩ D, A ∩ B, hC.inter hD, hA.inter hB, ?_⟩
  ext p
  simp only [mem_inter_iff, mem_prod]
  tauto

theorem base_inter_finite {E H : Set Space} (hE : E ∈ compactRectangles)
    (hH : H ∈ compactFinite) : E ∩ H ∈ compactFinite := by
  have hb : compactRectangles ⊆ {H | E ∩ H ∈ compactFinite} :=
    fun H hH => subset_supClosure (base_inter hE hH)
  have hc : SupClosed {H : Set Space | E ∩ H ∈ compactFinite} := by
    intro H hH K hK
    change E ∩ (H ∪ K) ∈ compactFinite
    rw [inter_union_distrib_left]
    exact compact_union hH hK
  exact supClosure_min hb hc hH

theorem compact_inter {E H : Set Space} (hE : E ∈ compactFinite) (hH : H ∈ compactFinite) :
    E ∩ H ∈ compactFinite := by
  have hb : compactRectangles ⊆ {E | E ∩ H ∈ compactFinite} :=
    fun E hE => base_inter_finite hE hH
  have hc : SupClosed {E : Set Space | E ∩ H ∈ compactFinite} := by
    intro E hE K hK
    change (E ∪ K) ∩ H ∈ compactFinite
    rw [union_inter_distrib_right]
    exact compact_union hE hK
  exact supClosure_min hb hc hE

theorem fiber_compact {E : Set Space} (hE : E ∈ compactFinite)
    (ω : IBMSourceLaws.JointSample) : IsCompact (fiber E ω) := by
  have hb : compactRectangles ⊆ {E | IsCompact (fiber E ω)} := by
    rintro E ⟨C, A, hC, _, rfl⟩
    change IsCompact (fiber (C ×ˢ A) ω)
    by_cases hω : ω ∈ A
    · simpa only [fiber, mem_prod, hω, and_true, ofPred_mem_eq] using hC
    · simpa only [fiber, mem_prod, hω, and_false, ofPred_false] using
        (isCompact_empty : IsCompact (∅ : Set ℝ≥0))
  have hc : SupClosed {E : Set Space | IsCompact (fiber E ω)} := by
    intro E hE H hH
    change IsCompact (fiber E ω ∪ fiber H ω)
    exact (show IsCompact (fiber E ω) from hE).union hH
  exact supClosure_min hb hc hE

theorem projection_union (E H : Set Space) : projection (E ∪ H) = projection E ∪ projection H := by
  ext ω
  simp only [projection, fiber, mem_ofPred_eq, Set.Nonempty, mem_union, exists_or]

theorem projection_measurable {E : Set Space} (hE : E ∈ compactFinite) :
    MeasurableSet (projection E) := by
  have hb : compactRectangles ⊆ {E | MeasurableSet (projection E)} := by
    rintro E ⟨C, A, _, hA, rfl⟩
    change MeasurableSet (projection (C ×ˢ A))
    by_cases hC : C.Nonempty
    · have he : projection (C ×ˢ A) = A := by
        ext ω
        constructor
        · exact fun ⟨r, hr⟩ => hr.2
        · exact fun hω => ⟨hC.choose, hC.choose_spec, hω⟩
      rw [he]
      exact hA
    · have he : projection (C ×ˢ A) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        exact fun ω ⟨r, hr⟩ => hC ⟨r, hr.1⟩
      rw [he]
      exact MeasurableSet.empty
  have hc : SupClosed {E : Set Space | MeasurableSet (projection E)} := by
    intro E hE H hH
    change MeasurableSet (projection (E ∪ H))
    rw [projection_union]
    exact (show MeasurableSet (projection E) from hE).union hH
  exact supClosure_min hb hc hE

def closedPrefix (K : ℕ → Set Space) : ℕ → Set Space
  | 0 => K 0
  | n+1 => closedPrefix K n ∩ K (n+1)

theorem closedPrefix_mem (K : ℕ → Set Space) (hK : ∀ n, K n ∈ compactFinite) (n : ℕ) :
    closedPrefix K n ∈ compactFinite := by
  induction n with
  | zero => exact hK 0
  | succ n ih => exact compact_inter ih (hK (n+1))

theorem closedPrefix_antitone (K : ℕ → Set Space) : Antitone (closedPrefix K) :=
  antitone_nat_of_succ_le fun _ => inter_subset_left

theorem closedPrefix_subset (K : ℕ → Set Space) (n : ℕ) : closedPrefix K n ⊆ K n := by
  cases n with
  | zero => exact Subset.rfl
  | succ n => exact inter_subset_right

theorem mem_closedPrefix (K : ℕ → Set Space) (n : ℕ) (p : Space) :
    p ∈ closedPrefix K n ↔ ∀ i ≤ n, p ∈ K i := by
  induction n with
  | zero =>
    constructor
    · intro h i hi
      have he : i = 0 := Nat.eq_zero_of_le_zero hi
      simpa only [he, closedPrefix] using h
    · intro h
      change p ∈ K 0
      exact h 0 le_rfl
  | succ n ih =>
    change (p ∈ closedPrefix K n ∩ K (n+1)) ↔ _
    rw [mem_inter_iff, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases eq_or_lt_of_le hi with he | hi
      · simpa only [he] using hn
      · exact h i (Nat.le_of_lt_succ hi)
    · intro h
      exact ⟨fun i hi => h i (hi.trans (Nat.le_succ n)), h (n+1) le_rfl⟩

theorem closedPrefix_inter_empty (K : ℕ → Set Space) (he : (⋂ n, K n) = ∅) :
    (⋂ n, closedPrefix K n) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hh : p ∈ ⋂ n, K n := mem_iInter.mpr fun n => closedPrefix_subset K n (mem_iInter.mp hp n)
  simp only [he, mem_empty_iff_false] at hh

theorem eventual_projection_exit (K : ℕ → Set Space) (hK : ∀ n, K n ∈ compactFinite)
    (hm : Antitone K) (he : (⋂ n, K n) = ∅) (ω : IBMSourceLaws.JointSample) :
    ∀ᶠ n in atTop, ω ∉ projection (K n) := by
  have hn : ∃ N, ¬(fiber (K N) ω).Nonempty := by
    by_contra h
    push Not at h
    obtain ⟨r, hr⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => fiber (K n) ω) (fun n r hr => hm (Nat.le_succ n) hr) h
      (fiber_compact (hK 0) ω) (fun n => (fiber_compact (hK n) ω).isClosed)
    have hp : (r,ω) ∈ ⋂ n, K n := mem_iInter.mpr fun n => mem_iInter.mp hr n
    simp only [he, mem_empty_iff_false] at hp
  obtain ⟨N, hN⟩ := hn
  exact eventually_atTop.mpr ⟨N, fun n hn ⟨r, hr⟩ => hN ⟨r, hm hn hr⟩⟩

theorem closedPrefix_projection_exit (K : ℕ → Set Space) (hK : ∀ n, K n ∈ compactFinite)
    (he : (⋂ n, K n) = ∅) (ω : IBMSourceLaws.JointSample) :
    ∀ᶠ n in atTop, ω ∉ projection (closedPrefix K n) :=
  eventual_projection_exit (closedPrefix K) (closedPrefix_mem K hK) (closedPrefix_antitone K)
    (closedPrefix_inter_empty K he) ω

end OperatorDerivativeRewrite.Foundation.IBMCompactPredictableFibers
