import Foundation.IBMGermSupportContinuity
import Mathlib.MeasureTheory.SetSemiring

/-! The actual raw-IBM predictable rectangle semiring and its finite-union ring. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableRectangles
open IBMNaturalFiltrationObstruction
set_option backward.isDefEq.respectTransparency false

abbrev Space := ℝ≥0 × IBMSourceLaws.JointSample

def rect (s t : ℝ≥0) (A : Set IBMSourceLaws.JointSample) : Set Space := Ioc s t ×ˢ A

def rectangles : Set (Set Space) :=
  {E | ∃ s t A, s ≤ t ∧ MeasurableSet[naturalFiltration s] A ∧ E = rect s t A}

theorem rect_mem (s t : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[naturalFiltration s] A) : rect s t A ∈ rectangles := by
  refine ⟨s, max s t, A, le_max_left _ _, hA, ?_⟩
  ext ⟨r, ω⟩
  simp only [rect, mem_prod, mem_Ioc]
  constructor
  · exact fun h => ⟨⟨h.1.1, h.1.2.trans (le_max_right _ _)⟩, h.2⟩
  · rintro ⟨⟨hsr, hr⟩, ha⟩
    exact ⟨⟨hsr, (le_max_iff.mp hr).resolve_left (not_le_of_gt hsr)⟩, ha⟩

theorem rect_predictable (s t : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[naturalFiltration s] A) :
    MeasurableSet[naturalFiltration.predictable] (rect s t A) :=
  measurableSet_predictable_Ioc_prod s t hA

theorem rect_inter (s t u v : ℝ≥0) (A B : Set IBMSourceLaws.JointSample) :
    rect s t A ∩ rect u v B = rect (max s u) (min t v) (A ∩ B) := by
  ext ⟨r, ω⟩
  simp only [rect, mem_inter_iff, mem_prod, mem_Ioc, max_lt_iff, le_min_iff]
  tauto

theorem rect_disjoint {s t u v : ℝ≥0} (htu : t ≤ u)
    (A B : Set IBMSourceLaws.JointSample) : Disjoint (rect s t A) (rect u v B) := by
  apply disjoint_left.mpr
  intro p hp hq
  exact (not_lt_of_ge (hp.1.2.trans htu)) hq.1.1

theorem rect_difference (s t u v : ℝ≥0) (A B : Set IBMSourceLaws.JointSample) :
    rect s t A \ rect u v B =
      rect s (min t u) A ∪ (rect (max s u) (min t v) (A \ B) ∪ rect (max s v) t A) := by
  ext ⟨r, ω⟩
  constructor
  · rintro ⟨⟨⟨hsr, hrt⟩, ha⟩, hn⟩
    by_cases hru : r ≤ u
    · exact Or.inl ⟨⟨hsr, le_min hrt hru⟩, ha⟩
    by_cases hrv : r ≤ v
    · exact Or.inr (Or.inl ⟨⟨max_lt hsr (lt_of_not_ge hru), le_min hrt hrv⟩,
        ha, fun hb => hn ⟨⟨lt_of_not_ge hru, hrv⟩, hb⟩⟩)
    · exact Or.inr (Or.inr ⟨⟨max_lt hsr (lt_of_not_ge hrv), hrt⟩, ha⟩)
  · rintro (h | h | h)
    · exact ⟨⟨⟨h.1.1, h.1.2.trans (min_le_left _ _)⟩, h.2⟩,
        fun he => (not_lt_of_ge (h.1.2.trans (min_le_right _ _))) he.1.1⟩
    · exact ⟨⟨⟨(le_max_left _ _).trans_lt h.1.1, h.1.2.trans (min_le_left _ _)⟩, h.2.1⟩,
        fun he => h.2.2 he.2⟩
    · exact ⟨⟨⟨(le_max_left _ _).trans_lt h.1.1, h.1.2⟩, h.2⟩,
        fun he => (not_le_of_gt ((le_max_right _ _).trans_lt h.1.1)) he.1.2⟩

theorem rectangle_semiring : IsSetSemiring rectangles where
  empty_mem := by
    refine ⟨0, 0, ∅, le_rfl, ?_, ?_⟩
    · exact @MeasurableSet.empty _ (naturalFiltration 0)
    · simp only [rect, Ioc_self, empty_prod]
  inter_mem := by
    rintro E ⟨s, t, A, _, hA, rfl⟩ F ⟨u, v, B, _, hB, rfl⟩
    rw [rect_inter]
    exact rect_mem _ _ _ (((naturalFiltration.mono (le_max_left s u)) _ hA).inter
      ((naturalFiltration.mono (le_max_right s u)) _ hB))
  sdiff_eq_sUnion' := by
    classical
    rintro E ⟨s, t, A, _, hA, rfl⟩ F ⟨u, v, B, huv, hB, rfl⟩
    let P := rect s (min t u) A
    let Q := rect (max s u) (min t v) (A \ B)
    let R := rect (max s v) t A
    have hP : P ∈ rectangles := rect_mem _ _ _ hA
    have hQ : Q ∈ rectangles := rect_mem _ _ _
      (((naturalFiltration.mono (le_max_left s u)) _ hA).diff
        ((naturalFiltration.mono (le_max_right s u)) _ hB))
    have hR : R ∈ rectangles := rect_mem _ _ _ ((naturalFiltration.mono (le_max_left s v)) _ hA)
    have hPQ : Disjoint P Q := rect_disjoint ((min_le_right t u).trans (le_max_right s u)) _ _
    have hQR : Disjoint Q R := rect_disjoint ((min_le_right t v).trans (le_max_right s v)) _ _
    have hPR : Disjoint P R := rect_disjoint
      ((min_le_right t u).trans (huv.trans (le_max_right s v))) _ _
    refine ⟨{P, Q, R}, ?_, ?_, ?_⟩
    · intro H hH
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl | rfl <;> assumption
    · intro H hH K hK hne
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hH hK
      rcases hH with rfl | rfl | rfl <;> rcases hK with rfl | rfl | rfl
      · exact (hne rfl).elim
      · exact hPQ
      · exact hPR
      · exact hPQ.symm
      · exact (hne rfl).elim
      · exact hQR
      · exact hPR.symm
      · exact hQR.symm
      · exact (hne rfl).elim
    · simpa only [Finset.coe_insert, Finset.coe_singleton, sUnion_insert, sUnion_singleton]
        using rect_difference s t u v A B

def elementaryRing : Set (Set Space) := supClosure rectangles

theorem elementary_isSetRing : IsSetRing elementaryRing := rectangle_semiring.isSetRing_supClosure

theorem elementary_predictable {E : Set Space} (hE : E ∈ elementaryRing) :
    MeasurableSet[naturalFiltration.predictable] E := by
  have hb : rectangles ⊆ {E | MeasurableSet[naturalFiltration.predictable] E} := by
    rintro R ⟨s, t, A, _, hA, rfl⟩
    exact rect_predictable s t A hA
  have hc : SupClosed {E : Set Space | MeasurableSet[naturalFiltration.predictable] E} := by
    intro R hR S hS
    exact (show MeasurableSet[naturalFiltration.predictable] R from hR).union hS
  exact supClosure_min hb hc hE

theorem elementary_bounded {E : Set Space} (hE : E ∈ elementaryRing) :
    ∃ T : ℝ≥0, E ⊆ rect 0 T univ := by
  have hb : rectangles ⊆ {E | ∃ T : ℝ≥0, E ⊆ rect 0 T univ} := by
    rintro R ⟨s, t, A, _, _, rfl⟩
    exact ⟨t, fun p hp => ⟨⟨(zero_le : 0 ≤ s).trans_lt hp.1.1, hp.1.2⟩, mem_univ _⟩⟩
  have hc : SupClosed {E : Set Space | ∃ T : ℝ≥0, E ⊆ rect 0 T univ} := by
    rintro R ⟨T, hT⟩ S ⟨U, hU⟩
    refine ⟨max T U, ?_⟩
    rintro p (hp | hp)
    · exact ⟨⟨(hT hp).1.1, (hT hp).1.2.trans (le_max_left _ _)⟩, mem_univ _⟩
    · exact ⟨⟨(hU hp).1.1, (hU hp).1.2.trans (le_max_right _ _)⟩, mem_univ _⟩
  exact supClosure_min hb hc hE

def generators : Set (Set Space) := elementaryRing ∪
  {E | ∃ A, MeasurableSet[naturalFiltration 0] A ∧ E = {0} ×ˢ A}

theorem predictable_generation :
    MeasurableSpace.generateFrom generators = naturalFiltration.predictable := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro E (hE | ⟨A, hA, rfl⟩)
    · exact elementary_predictable hE
    · exact measurableSet_predictable_singleton_bot_prod hA
  · apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨A, hA, rfl⟩)
    · intro s A hA
      have he : Ioi s ×ˢ A = ⋃ n : ℕ, rect s n A := by
        ext ⟨r, ω⟩
        simp only [mem_prod, mem_Ioi, mem_iUnion, rect, mem_Ioc]
        constructor
        · rintro ⟨hsr, ha⟩
          obtain ⟨n, hn⟩ := exists_nat_ge r
          exact ⟨n, ⟨hsr, hn⟩, ha⟩
        · rintro ⟨n, ⟨hsr, _⟩, ha⟩
          exact ⟨hsr, ha⟩
      rw [he]
      exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
        (Or.inl (subset_supClosure (rect_mem s n A hA)))

end OperatorDerivativeRewrite.Foundation.IBMPredictableRectangles
