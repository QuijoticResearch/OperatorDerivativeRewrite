import Foundation.IBMPredictableFiniteIntegral
import Mathlib.MeasureTheory.Measure.AddContent

/-! Actual finite additive predictable content; countable extension is not assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableRingContent
open IBMPredictableRectangles IBMPredictableFiniteIntegral
open IBMTimeAveragedObservable IBMWeightedTerminalEnergy IBMGermPredictableStep
set_option backward.isDefEq.respectTransparency false

theorem partition_indicator_sum {E : Set Space} (P : Finpartition E) :
    (∑ R ∈ P.parts, R.indicator (fun _ => (1 : ℝ))) = E.indicator (fun _ => 1) := by
  classical
  have hc : ⋃₀ (P.parts : Set (Set Space)) = E := by
    simpa only [Finset.sup_id_set_eq_sUnion] using P.sup_parts
  funext p
  simp only [Finset.sum_apply]
  by_cases hp : p ∈ E
  · obtain ⟨R, hR, hpR⟩ := mem_sUnion.mp (hc.symm ▸ hp)
    rw [Finset.sum_eq_single R]
    · simp only [indicator_of_mem hpR, indicator_of_mem hp]
    · intro Q hQ hQR
      have hn : p ∉ Q := fun hpQ => disjoint_left.mp (P.disjoint hR hQ hQR.symm) hpR hpQ
      simp only [indicator_of_notMem hn]
    · exact fun hn => (hn hR).elim
  · rw [indicator_of_notMem hp]
    exact Finset.sum_eq_zero fun R hR => indicator_of_notMem (fun hpR => hp (P.le hR hpR)) _

theorem rectangle_indicator_mem {E : Set Space} (hE : E ∈ rectangles) :
    E.indicator (fun _ => (1 : ℝ)) ∈ processSpace := by
  obtain ⟨s, t, A, hst, hA, rfl⟩ := hE
  exact basis_mem (⟨(s,t,A), hst, hA⟩ : Index)

theorem ring_indicator_mem {E : Set Space} (hE : E ∈ elementaryRing) :
    E.indicator (fun _ => (1 : ℝ)) ∈ processSpace := by
  obtain ⟨P, hP⟩ := rectangle_semiring.mem_supClosure_iff.mp hE
  rw [← partition_indicator_sum P]
  exact processSpace.sum_mem fun R hR => rectangle_indicator_mem (hP hR)

def indicatorClass (E : Set Space) : processSpace := by
  classical
  exact if hE : E ∈ elementaryRing then
    ⟨E.indicator (fun _ => 1), ring_indicator_mem hE⟩ else 0

theorem indicatorClass_value {E : Set Space} (hE : E ∈ elementaryRing) :
    (indicatorClass E : Space → ℝ) = E.indicator (fun _ => 1) := by
  simp only [indicatorClass, dite_eq_left hE]

theorem indicatorClass_empty : indicatorClass ∅ = 0 := by
  apply Subtype.ext
  rw [indicatorClass_value elementary_isSetRing.empty_mem]
  exact indicator_empty _

theorem disjoint_indicator_sum (I : Finset (Set Space))
    (hd : PairwiseDisjoint (I : Set (Set Space)) id) :
    (∑ R ∈ I, R.indicator (fun _ => (1 : ℝ))) =
      (⋃₀ (I : Set (Set Space))).indicator (fun _ => 1) := by
  classical
  have hs := partition_indicator_sum (Finpartition.ofPairwiseDisjoint I hd)
  rw [Finpartition.sum_ofPairwiseDisjoint_eq_sum hd (indicator_empty _)] at hs
  simpa only [Finset.sup_id_set_eq_sUnion] using hs

theorem indicatorClass_sUnion (I : Finset (Set Space)) (hI : ↑I ⊆ elementaryRing)
    (hd : PairwiseDisjoint (I : Set (Set Space)) id)
    (hU : ⋃₀ (I : Set (Set Space)) ∈ elementaryRing) :
    indicatorClass (⋃₀ (I : Set (Set Space))) = ∑ R ∈ I, indicatorClass R := by
  apply Subtype.ext
  change processSpace.subtype (indicatorClass _) = processSpace.subtype (∑ R ∈ I, indicatorClass R)
  rw [map_sum]
  change (indicatorClass _ : Space → ℝ) = ∑ R ∈ I, (indicatorClass R : Space → ℝ)
  rw [indicatorClass_value hU, ← disjoint_indicator_sum I hd]
  exact Finset.sum_congr rfl fun R hR => (indicatorClass_value (hI hR)).symm

def ringIntegral (F : JointL2) (E : Set Space) : JointL2 := integral F (indicatorClass E)

theorem ringIntegral_empty (F : JointL2) : ringIntegral F ∅ = 0 := by
  rw [ringIntegral, indicatorClass_empty, map_zero]

theorem ringIntegral_sUnion (F : JointL2) (I : Finset (Set Space)) (hI : ↑I ⊆ elementaryRing)
    (hd : PairwiseDisjoint (I : Set (Set Space)) id)
    (hU : ⋃₀ (I : Set (Set Space)) ∈ elementaryRing) :
    ringIntegral F (⋃₀ (I : Set (Set Space))) = ∑ R ∈ I, ringIntegral F R := by
  rw [ringIntegral, indicatorClass_sUnion I hI hd hU, map_sum]
  rfl

theorem ringIntegral_rect (F : JointL2) (s t : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hst : s ≤ t) (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) :
    ringIntegral F (rect s t A) = stepClass F s t (eventCoefficient s A hA) := by
  let d : Index := ⟨(s,t,A), hst, hA⟩
  have he : indicatorClass (rect s t A) = ⟨basisProcess d, basis_mem d⟩ := by
    apply Subtype.ext
    rw [indicatorClass_value (subset_supClosure (rect_mem s t A hA))]
    rfl
  rw [ringIntegral, he, integral_basis]
  rfl

theorem rectangle_pairing_nonneg (F : JointL2) {E : Set Space} (hE : E ∈ rectangles) :
    0 ≤ inner ℝ F (ringIntegral F E) := by
  obtain ⟨s, t, A, hst, hA, rfl⟩ := hE
  rw [ringIntegral_rect F s t A hst hA, idempotent_pairing F hst _ (ae_of_all _ fun ω => by
    by_cases ha : ω ∈ A <;> simp [eventCoefficient, Set.indicator, ha])]
  exact sq_nonneg _

theorem ring_pairing_nonneg (F : JointL2) {E : Set Space} (hE : E ∈ elementaryRing) :
    0 ≤ inner ℝ F (ringIntegral F E) := by
  obtain ⟨P, hP⟩ := rectangle_semiring.mem_supClosure_iff.mp hE
  have hc : ⋃₀ (P.parts : Set (Set Space)) = E := by
    simpa only [Finset.sup_id_set_eq_sUnion] using P.sup_parts
  rw [← hc, ringIntegral_sUnion F P.parts (fun R hR => subset_supClosure (hP hR))
    P.disjoint (hc.symm ▸ hE), inner_sum]
  exact Finset.sum_nonneg fun R hR => rectangle_pairing_nonneg F (hP hR)

def content (F : JointL2) : AddContent ℝ≥0∞ elementaryRing where
  toFun E := ENNReal.ofReal (inner ℝ F (ringIntegral F E))
  empty' := by rw [ringIntegral_empty, inner_zero_right, ENNReal.ofReal_zero]
  sUnion' I hI hd hU := by
    rw [ringIntegral_sUnion F I hI hd hU, inner_sum,
      ENNReal.ofReal_sum_of_nonneg (fun R hR => ring_pairing_nonneg F (hI hR))]

theorem content_actual_rectangle (F : JointL2) (s t : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hst : s ≤ t) (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) :
    content F (rect s t A) = incrementMeasure F s t A := by
  change ENNReal.ofReal (inner ℝ F (ringIntegral F (rect s t A))) = _
  rw [ringIntegral_rect F s t A hst hA, terminal_pairing F hst _,
    incrementMeasure_apply F s t (IBMNaturalFiltrationObstruction.naturalFiltration.le s A hA)]
  congr 1
  rw [← integral_indicator (IBMNaturalFiltrationObstruction.naturalFiltration.le s A hA)]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    by_cases ha : ω ∈ A <;> simp [eventCoefficient, Set.indicator, ha]

theorem content_bound (F : JointL2) {E : Set Space} (hE : E ∈ elementaryRing) :
    content F E ≤ ENNReal.ofReal (‖F‖ ^ 2) := by
  obtain ⟨T, hT⟩ := elementary_bounded hE
  have hU : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration 0]
      (univ : Set IBMSourceLaws.JointSample) := @MeasurableSet.univ _ _
  have hm := addContent_mono (m := content F) elementary_isSetRing.isSetSemiring hE
    (subset_supClosure (rect_mem 0 T univ hU)) hT
  have he : incrementMeasure F 0 T univ = IBMTerminalEnergyMeasure.energyMeasure F (Ioc 0 T) := by
    rw [incrementMeasure_apply F 0 T MeasurableSet.univ, setIntegral_univ,
      ← IBMTerminalEnergyMeasure.actual_increment_energy,
      IBMTerminalEnergyMeasure.energyMeasure_increment F (zero_le : 0 ≤ T)]
  rw [content_actual_rectangle F 0 T univ (zero_le : 0 ≤ T) hU, he] at hm
  exact hm.trans (IBMTerminalEnergyMeasure.interval_bound F 0 T)

theorem rectangle_pairing_energy (F : JointL2) {E : Set Space} (hE : E ∈ rectangles) :
    inner ℝ F (ringIntegral F E) = ‖ringIntegral F E‖ ^ 2 := by
  obtain ⟨s, t, A, hst, hA, rfl⟩ := hE
  rw [ringIntegral_rect F s t A hst hA]
  exact idempotent_pairing F hst _ (ae_of_all _ fun ω => by
    by_cases ha : ω ∈ A <;> simp [eventCoefficient, Set.indicator, ha])

theorem disjoint_rectangle_orthogonal (F : JointL2) {E H : Set Space}
    (hE : E ∈ rectangles) (hH : H ∈ rectangles) (hd : Disjoint E H) :
    inner ℝ (ringIntegral F E) (ringIntegral F H) = 0 := by
  obtain ⟨s, t, A, hst, hA, rfl⟩ := hE
  obtain ⟨u, v, B, huv, hB, rfl⟩ := hH
  rw [ringIntegral_rect F s t A hst hA, ringIntegral_rect F u v B huv hB]
  rcases disjoint_prod.mp hd with htime | hspace
  · rcases hst.eq_or_lt with he | hpos
    · subst t
      rw [stepClass_self, inner_zero_left]
    rcases huv.eq_or_lt with he | hpos'
    · subst v
      rw [stepClass_self, inner_zero_right]
    have hsep : t ≤ u ∨ v ≤ s := by
      by_cases ht : t ≤ u
      · exact Or.inl ht
      right
      by_contra hv
      exact disjoint_left.mp htime
        (show min t v ∈ Ioc s t from
          ⟨lt_min hpos (lt_of_not_ge hv), min_le_left _ _⟩)
        (show min t v ∈ Ioc u v from
          ⟨lt_min (lt_of_not_ge ht) hpos', min_le_right _ _⟩)
    rcases hsep with h | h
    · exact disjoint_steps_orthogonal F hst h huv _ _
    · rw [real_inner_comm]
      exact disjoint_steps_orthogonal F huv h hst _ _
  · rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [stepClass_ae F hst (eventCoefficient s A hA),
      stepClass_ae F huv (eventCoefficient u B hB)] with ω he hh
    rw [he, hh, Real.inner_apply]
    by_cases ha : ω ∈ A
    · have hb : ω ∉ B := fun hb => disjoint_left.mp hspace ha hb
      simp [eventCoefficient, Set.indicator, ha, hb]
    · simp [eventCoefficient, Set.indicator, ha]

theorem ring_pairing_energy (F : JointL2) {E : Set Space} (hE : E ∈ elementaryRing) :
    inner ℝ F (ringIntegral F E) = ‖ringIntegral F E‖ ^ 2 := by
  classical
  obtain ⟨P, hP⟩ := rectangle_semiring.mem_supClosure_iff.mp hE
  have hc : ⋃₀ (P.parts : Set (Set Space)) = E := by
    simpa only [Finset.sup_id_set_eq_sUnion] using P.sup_parts
  have he : ringIntegral F E = ∑ R ∈ P.parts, ringIntegral F R := by
    calc
      ringIntegral F E = ringIntegral F (⋃₀ (P.parts : Set (Set Space))) :=
        congrArg (ringIntegral F) hc.symm
      _ = _ := ringIntegral_sUnion F P.parts (fun R hR => subset_supClosure (hP hR))
        P.disjoint (hc.symm ▸ hE)
  rw [he, inner_sum, ← real_inner_self_eq_norm_sq, inner_sum]
  apply Finset.sum_congr rfl
  intro R hR
  rw [sum_inner, Finset.sum_eq_single R]
  · exact rectangle_pairing_energy F (hP hR) |>.trans (real_inner_self_eq_norm_sq _).symm
  · intro S hS hSR
    exact disjoint_rectangle_orthogonal F (hP hS) (hP hR) (P.disjoint hS hR hSR)
  · exact fun hn => (hn hR).elim

theorem content_energy (F : JointL2) {E : Set Space} (hE : E ∈ elementaryRing) :
    content F E = ENNReal.ofReal (‖ringIntegral F E‖ ^ 2) := by
  change ENNReal.ofReal (inner ℝ F (ringIntegral F E)) = _
  rw [ring_pairing_energy F hE]

theorem ringIntegral_support (F : JointL2) {E : Set Space} (hE : E ∈ elementaryRing)
    (A : Set IBMSourceLaws.JointSample) (hs : E ⊆ univ ×ˢ A) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ω ∉ A → ringIntegral F E ω = 0 := by
  apply integral_support F (indicatorClass E) A
  intro r ω hn
  rw [indicatorClass_value hE]
  exact indicator_of_notMem (fun hp => hn (hs hp).2) _

theorem ring_energy_support_bound (F : JointL2) {E : Set Space} (hE : E ∈ elementaryRing)
    (A : Set IBMSourceLaws.JointSample) (hA : MeasurableSet A) (hs : E ⊆ univ ×ˢ A) :
    ‖ringIntegral F E‖ ^ 2 ≤ ∫ ω in A, F ω ^ 2 ∂IBMSourceLaws.jointMeasure := by
  have he : inner ℝ (IBMGermIndicatorSupport.supportedTerminal F A hA) (ringIntegral F E) =
      inner ℝ F (ringIntegral F E) := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [IBMGermIndicatorSupport.supportedTerminal_ae F A hA,
      ringIntegral_support F hE A hs] with ω hf hz
    rw [hf, Real.inner_apply, Real.inner_apply]
    by_cases hn : ω ∈ A
    · simp only [indicator_of_mem hn]
    · rw [indicator_of_notMem hn, hz hn, mul_zero, mul_zero]
  have hn := sq_nonneg ‖IBMGermIndicatorSupport.supportedTerminal F A hA - ringIntegral F E‖
  rw [norm_sub_sq_real, he, ring_pairing_energy F hE] at hn
  rw [← IBMGermIndicatorSupport.supportedTerminal_energy F A hA]
  linarith

theorem content_support_bound (F : JointL2) {E : Set Space} (hE : E ∈ elementaryRing)
    (A : Set IBMSourceLaws.JointSample) (hA : MeasurableSet A) (hs : E ⊆ univ ×ˢ A) :
    content F E ≤ ENNReal.ofReal (∫ ω in A, F ω ^ 2 ∂IBMSourceLaws.jointMeasure) := by
  rw [content_energy F hE]
  exact ENNReal.ofReal_le_ofReal (ring_energy_support_bound F hE A hA hs)

theorem ring_integrals_tendsto_zero (F : JointL2) (E : ℕ → Set Space)
    (hE : ∀ n, E n ∈ elementaryRing) (A : ℕ → Set IBMSourceLaws.JointSample)
    (hA : ∀ n, MeasurableSet (A n)) (hs : ∀ n, E n ⊆ univ ×ˢ A n)
    (hvanish : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ∀ᶠ n in atTop, ω ∉ A n) :
    Tendsto (fun n => ringIntegral F (E n)) atTop (𝓝 0) :=
  IBMGermSupportContinuity.supported_classes_tendsto_zero F _ A hA hvanish
    (fun n => ring_energy_support_bound F (hE n) (A n) (hA n) (hs n))

end OperatorDerivativeRewrite.Foundation.IBMPredictableRingContent
