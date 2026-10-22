import Foundation.IBMPredictableContentContinuity
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

/-! An actual energy measure on the full raw-IBM predictable sigma algebra. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMJointPredictableEnergyMeasure
open IBMPredictableRectangles IBMPredictableRingContent IBMPredictableContentContinuity
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction IBMWeightedTerminalEnergy
set_option backward.isDefEq.respectTransparency false

def origin (A : Set IBMSourceLaws.JointSample) : Set Space := {0} ×ˢ A

def positivePart (E : Set Space) : Set Space := E ∩ (Ioi 0 ×ˢ univ)

theorem ring_disjoint_origin {E : Set Space} (hE : E ∈ elementaryRing)
    (A : Set IBMSourceLaws.JointSample) : Disjoint E (origin A) := by
  obtain ⟨T, hT⟩ := elementary_bounded hE
  apply disjoint_left.mpr
  intro p hp ho
  have hz : p.1 = 0 := ho.1
  have hh := (hT hp).1.1
  rw [hz] at hh
  exact (lt_irrefl (0 : ℝ≥0)) hh

theorem origin_inter (A B : Set IBMSourceLaws.JointSample) :
    origin A ∩ origin B = origin (A ∩ B) := by
  ext ⟨r,ω⟩
  by_cases hr : r = 0 <;> simp [origin, hr]

theorem origin_difference (A B : Set IBMSourceLaws.JointSample) :
    origin A \ origin B = origin (A \ B) := by
  ext ⟨r,ω⟩
  by_cases hr : r = 0 <;> simp [origin, hr]

theorem generators_inter {E H : Set Space} (hE : E ∈ generators) (hH : H ∈ generators) :
    E ∩ H ∈ generators := by
  rcases hE with hE | ⟨A, hA, rfl⟩ <;> rcases hH with hH | ⟨B, hB, rfl⟩
  · exact Or.inl (elementary_isSetRing.inter_mem hE hH)
  · change E ∩ origin B ∈ generators
    rw [show E ∩ origin B = ∅ from (ring_disjoint_origin hE B).eq_bot]
    exact Or.inl elementary_isSetRing.empty_mem
  · change origin A ∩ H ∈ generators
    rw [show origin A ∩ H = ∅ from (ring_disjoint_origin hH A).symm.eq_bot]
    exact Or.inl elementary_isSetRing.empty_mem
  · exact Or.inr ⟨A ∩ B, hA.inter hB, origin_inter A B⟩

theorem generators_difference {E H : Set Space} (hE : E ∈ generators) (hH : H ∈ generators) :
    E \ H ∈ generators := by
  rcases hE with hE | ⟨A, hA, rfl⟩ <;> rcases hH with hH | ⟨B, hB, rfl⟩
  · exact Or.inl (elementary_isSetRing.sdiff_mem hE hH)
  · change E \ origin B ∈ generators
    rw [(ring_disjoint_origin hE B).sdiff_eq_left]
    exact Or.inl hE
  · change origin A \ H ∈ generators
    rw [(ring_disjoint_origin hH A).symm.sdiff_eq_left]
    exact Or.inr ⟨A, hA, rfl⟩
  · exact Or.inr ⟨A \ B, hA.diff hB, origin_difference A B⟩

theorem generators_semiring : IsSetSemiring generators where
  empty_mem := Or.inl elementary_isSetRing.empty_mem
  inter_mem := fun _ hE _ hH => generators_inter hE hH
  sdiff_eq_sUnion' := by
    classical
    intro E hE H hH
    refine ⟨{E \ H}, ?_, ?_, ?_⟩
    · simpa only [Finset.coe_singleton, singleton_subset_iff] using generators_difference hE hH
    · simpa only [Finset.coe_singleton] using
        (pairwiseDisjoint_singleton (E \ H) (id : Set Space → Set Space))
    · simp only [Finset.coe_singleton, sUnion_singleton]

theorem content_zero_of_not_ring (F : JointL2) {E : Set Space}
    (hE : E ∉ elementaryRing) :
    content F E = 0 := by
  change ENNReal.ofReal (inner ℝ F (ringIntegral F E)) = 0
  rw [ringIntegral, indicatorClass, dite_eq_right hE, map_zero, inner_zero_right,
    ENNReal.ofReal_zero]

theorem ring_origin_subset_empty {E : Set Space} (hE : E ∈ elementaryRing)
    (hs : E ⊆ origin univ) : E = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  exact fun p hp => disjoint_left.mp (ring_disjoint_origin hE univ) hp (hs hp)

theorem content_zero_on_origin (F : JointL2) {E : Set Space} (hs : E ⊆ origin univ) :
    content F E = 0 := by
  by_cases hE : E ∈ elementaryRing
  · rw [ring_origin_subset_empty hE hs, addContent_empty]
  · exact content_zero_of_not_ring F hE

def extendedContent (F : JointL2) : AddContent ℝ≥0∞ generators where
  toFun := content F
  empty' := addContent_empty
  sUnion' I hI hd hU := by
    rcases hU with hU | ⟨A, _hA, hUnion⟩
    · have hR : ↑I ⊆ elementaryRing := by
        intro E hE
        rcases hI hE with hE' | ⟨B, _hB, hEb⟩
        · exact hE'
        · have hsub : E ⊆ ⋃₀ (I : Set (Set Space)) := subset_sUnion_of_mem hE
          have hz : E = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            intro p hp
            have hb : p ∈ {0} ×ˢ B := hEb ▸ hp
            exact disjoint_left.mp (ring_disjoint_origin hU B) (hsub hp) hb
          rw [hz]
          exact elementary_isSetRing.empty_mem
      exact addContent_sUnion hR hd hU
    · have hsub : ⋃₀ (I : Set (Set Space)) ⊆ origin univ := by
        rw [hUnion]
        exact fun p hp => ⟨hp.1, mem_univ _⟩
      rw [content_zero_on_origin F hsub]
      symm
      exact Finset.sum_eq_zero fun E hE => content_zero_on_origin F
        ((subset_sUnion_of_mem hE).trans hsub)

theorem positivePart_ring {E : Set Space} (hE : E ∈ elementaryRing) : positivePart E = E := by
  obtain ⟨T, hT⟩ := elementary_bounded hE
  apply inter_eq_left.mpr
  exact fun p hp => ⟨(hT hp).1.1, mem_univ _⟩

theorem positivePart_origin (A : Set IBMSourceLaws.JointSample) : positivePart (origin A) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hz : p.1 = 0 := hp.1.1
  have hh := hp.2.1
  rw [hz] at hh
  exact (lt_irrefl (0 : ℝ≥0)) hh

theorem generator_positivePart (F : JointL2) {E : Set Space} (hE : E ∈ generators) :
    positivePart E ∈ elementaryRing ∧ content F E = content F (positivePart E) := by
  rcases hE with hE | ⟨A, _hA, rfl⟩
  · rw [positivePart_ring hE]
    exact ⟨hE, rfl⟩
  · change positivePart (origin A) ∈ elementaryRing ∧
      content F (origin A) = content F (positivePart (origin A))
    rw [positivePart_origin]
    refine ⟨elementary_isSetRing.empty_mem, ?_⟩
    rw [addContent_empty]
    exact content_zero_on_origin F (fun p hp => ⟨hp.1, mem_univ _⟩)

theorem extended_sigma_subadditive (F : JointL2) : (extendedContent F).IsSigmaSubadditive := by
  intro E hE hU
  have he : positivePart (⋃ n, E n) = ⋃ n, positivePart (E n) := by
    ext p
    simp only [positivePart, mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨⟨n, hn⟩, hp⟩
      exact ⟨n, hn, hp⟩
    · rintro ⟨n, hn, hp⟩
      exact ⟨⟨n, hn⟩, hp⟩
  have hh := content_sigma_subadditive F (fun n => (generator_positivePart (F := F) (hE n)).1)
    (he ▸ (generator_positivePart (F := F) hU).1)
  change content F (⋃ n, E n) ≤ ∑' n, content F (E n)
  rw [(generator_positivePart (F := F) hU).2, he]
  convert hh using 1
  exact tsum_congr fun n => (generator_positivePart (F := F) (hE n)).2

def predictableMeasure (F : JointL2) : @Measure Space naturalFiltration.predictable :=
  @AddContent.measure Space generators naturalFiltration.predictable (extendedContent F)
    generators_semiring predictable_generation.symm.le (extended_sigma_subadditive F)

theorem predictableMeasure_generator (F : JointL2) {E : Set Space} (hE : E ∈ generators) :
    predictableMeasure F E = content F E :=
  @AddContent.measure_eq Space generators E naturalFiltration.predictable (extendedContent F)
    generators_semiring predictable_generation.symm (extended_sigma_subadditive F) hE

theorem predictableMeasure_rectangle (F : JointL2) (s t : ℝ≥0)
    (A : Set IBMSourceLaws.JointSample) (hst : s ≤ t)
    (hA : MeasurableSet[naturalFiltration s] A) :
    predictableMeasure F (rect s t A) = incrementMeasure F s t A := by
  rw [predictableMeasure_generator F (Or.inl (subset_supClosure (rect_mem s t A hA))),
    content_actual_rectangle F s t A hst hA]

theorem predictableMeasure_origin (F : JointL2) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[naturalFiltration 0] A) : predictableMeasure F (origin A) = 0 := by
  have hm : origin A ∈ generators := Or.inr ⟨A, hA, rfl⟩
  rw [predictableMeasure_generator F hm]
  exact content_zero_on_origin F (fun p hp => ⟨hp.1, mem_univ _⟩)

theorem total_bound (F : JointL2) : predictableMeasure F univ ≤ ENNReal.ofReal (‖F‖ ^ 2) := by
  let : MeasurableSpace Space := naturalFiltration.predictable
  have hU : MeasurableSet[naturalFiltration 0]
      (univ : Set IBMSourceLaws.JointSample) := @MeasurableSet.univ _ _
  have hm : Monotone (fun n : ℕ => rect 0 n (univ : Set IBMSourceLaws.JointSample)) := by
    intro i j hij p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans (by exact_mod_cast hij)⟩, mem_univ _⟩
  have hB : predictableMeasure F (⋃ n : ℕ, rect 0 n univ) ≤ ENNReal.ofReal (‖F‖ ^ 2) := by
    rw [hm.measure_iUnion]
    apply iSup_le
    intro n
    rw [predictableMeasure_generator F (Or.inl (subset_supClosure (rect_mem 0 n univ hU)))]
    exact content_bound F (subset_supClosure (rect_mem 0 n univ hU))
  have hc : (univ : Set Space) = origin univ ∪ ⋃ n : ℕ, rect 0 n univ := by
    ext ⟨r,ω⟩
    constructor
    · intro _
      by_cases hr : r = 0
      · exact Or.inl ⟨hr, mem_univ _⟩
      · obtain ⟨n, hn⟩ := exists_nat_ge r
        exact Or.inr (mem_iUnion.mpr ⟨n, ⟨pos_iff_ne_zero.mpr hr, hn⟩, mem_univ _⟩)
    · exact fun _ => mem_univ _
  calc
    predictableMeasure F univ = predictableMeasure F (origin univ ∪ ⋃ n : ℕ, rect 0 n univ) :=
      congrArg (predictableMeasure F) hc
    _ ≤ predictableMeasure F (origin univ) + predictableMeasure F (⋃ n : ℕ, rect 0 n univ) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (‖F‖ ^ 2) := by
      rw [predictableMeasure_origin F univ hU, zero_add]
      exact hB

theorem finite_measure (F : JointL2) :
    @IsFiniteMeasure Space naturalFiltration.predictable (predictableMeasure F) := by
  constructor
  exact lt_of_le_of_lt (total_bound F) ENNReal.ofReal_lt_top

theorem observed_total_mass (t : ℝ≥0) :
    predictableMeasure (IBMDeterministicRangeObstruction.observed t) univ =
      ENNReal.ofReal (‖IBMDeterministicRangeObstruction.observed t‖ ^ 2) := by
  let F := IBMDeterministicRangeObstruction.observed t
  have hU : MeasurableSet[naturalFiltration 0]
      (univ : Set IBMSourceLaws.JointSample) := @MeasurableSet.univ _ _
  have he : predictableMeasure F (rect 0 t univ) = ENNReal.ofReal (‖F‖ ^ 2) := by
    rw [predictableMeasure_rectangle F 0 t univ (zero_le : 0 ≤ t) hU,
      incrementMeasure_apply F 0 t MeasurableSet.univ, setIntegral_univ,
      ← IBMTerminalEnergyMeasure.actual_increment_energy,
      IBMObservedInitialGerm.initial_channel_zero t,
      IBMObservedTerminalMartingale.terminal_class F
        (IBMDeterministicRangeObstruction.observed_mem_past t) le_rfl, sub_zero]
  exact le_antisymm (total_bound F) (he ▸ measure_mono (subset_univ (rect 0 t univ)))

end OperatorDerivativeRewrite.Foundation.IBMJointPredictableEnergyMeasure
