import Foundation.IBMPredictableCovarianceMeasure

/-! Exact mixed-channel stochastic energy on arbitrary predictable finite grids. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMMixedPredictableEnergy
open IBMTimeAveragedObservable IBMIntrinsicRightGerm IBMRightGermFiltration
open IBMIntrinsicMartingaleStep (Coefficient)
open IBMWeightedTerminalEnergy IBMGermPredictableStep IBMPredictableRectangles
open IBMPredictableFiniteIntegral IBMPredictableRingContent IBMPredictableFiniteIsometry
open IBMPredictableCovarianceMeasure

theorem mixed_disjoint_steps (F G : JointL2) {r u s t : ℝ≥0}
    (hru : r ≤ u) (hus : u ≤ s) (hst : s ≤ t) (a : Coefficient r) (b : Coefficient s) :
    inner ℝ (stepClass F r u a) (stepClass G s t b) = 0 :=
  past_inner_step_zero G hst b _
    (rightPast_mono hus (stepClass_mem_rightPast F hru a))

theorem mixed_disjoint_rectangle (F G : JointL2) {E H : Set Space}
    (hE : E ∈ rectangles) (hH : H ∈ rectangles) (hd : Disjoint E H) :
    inner ℝ (ringIntegral F E) (ringIntegral G H) = 0 := by
  obtain ⟨s, t, A, hst, hA, rfl⟩ := hE
  obtain ⟨u, v, B, huv, hB, rfl⟩ := hH
  rw [ringIntegral_rect F s t A hst hA, ringIntegral_rect G u v B huv hB]
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
    · exact mixed_disjoint_steps F G hst h huv _ _
    · rw [real_inner_comm]
      exact mixed_disjoint_steps G F huv h hst _ _
  · rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [stepClass_ae F hst (eventCoefficient s A hA),
      stepClass_ae G huv (eventCoefficient u B hB)] with ω he hh
    rw [he, hh, Real.inner_apply]
    by_cases ha : ω ∈ A
    · have hb : ω ∉ B := fun hb => disjoint_left.mp hspace ha hb
      simp [eventCoefficient, Set.indicator, ha, hb]
    · simp [eventCoefficient, Set.indicator, ha]

theorem mixed_disjoint_ring (F G : JointL2) {E H : Set Space}
    (hE : E ∈ elementaryRing) (hH : H ∈ elementaryRing) (hd : Disjoint E H) :
    inner ℝ (ringIntegral F E) (ringIntegral G H) = 0 := by
  classical
  obtain ⟨P, hP⟩ := rectangle_semiring.mem_supClosure_iff.mp hE
  obtain ⟨Q, hQ⟩ := rectangle_semiring.mem_supClosure_iff.mp hH
  have hp : ⋃₀ (P.parts : Set (Set Space)) = E := by
    simpa only [Finset.sup_id_set_eq_sUnion] using P.sup_parts
  have hq : ⋃₀ (Q.parts : Set (Set Space)) = H := by
    simpa only [Finset.sup_id_set_eq_sUnion] using Q.sup_parts
  rw [← hp, ringIntegral_sUnion F P.parts (fun R hR => subset_supClosure (hP hR))
    P.disjoint (hp.symm ▸ hE), ← hq,
    ringIntegral_sUnion G Q.parts (fun R hR => subset_supClosure (hQ hR))
      Q.disjoint (hq.symm ▸ hH), sum_inner]
  apply Finset.sum_eq_zero
  intro R hR
  rw [inner_sum]
  exact Finset.sum_eq_zero fun S hS =>
    mixed_disjoint_rectangle F G (hP hR) (hQ hS) (hd.mono (P.le hR) (Q.le hS))

theorem mixed_ring_intersection (F G : JointL2) {E H : Set Space}
    (hE : E ∈ elementaryRing) (hH : H ∈ elementaryRing) :
    inner ℝ (ringIntegral F E) (ringIntegral G H) = covariance F G (E ∩ H) := by
  have hI := elementary_isSetRing.inter_mem hE hH
  have hD := elementary_isSetRing.sdiff_mem hE hH
  have hB := elementary_isSetRing.sdiff_mem hH hE
  have he : ringIntegral F E = ringIntegral F (E \ H) + ringIntegral F (E ∩ H) := by
    rw [← ringIntegral_disjoint_union F hD hI disjoint_sdiff_inter, sdiff_union_inter]
  have hh : ringIntegral G H = ringIntegral G (H \ E) + ringIntegral G (E ∩ H) := by
    have hu : (H \ E) ∪ (E ∩ H) = H := by
      ext p
      simp only [mem_union, Set.mem_sdiff, mem_inter_iff]
      tauto
    have hd : Disjoint (H \ E) (E ∩ H) := disjoint_left.mpr fun _ h h' => h.2 h'.1
    rw [← ringIntegral_disjoint_union G hB hI hd, hu]
  nth_rw 1 [he]
  rw [inner_add_left, mixed_disjoint_ring F G hD hH disjoint_sdiff_left, zero_add,
    hh, inner_add_right, mixed_disjoint_ring F G hI hB
      (disjoint_left.mpr fun _ h h' => h'.2 h.1), zero_add, ← covariance_ring F G hI]

theorem basis_mixed_energy (F G : JointL2) (d e : Index) :
    inner ℝ (basisIntegral F d) (basisIntegral G e) =
      covariance F G (rect (left d) (right d) (event d) ∩ rect (left e) (right e) (event e)) := by
  have hd := subset_supClosure (rect_mem (left d) (right d) (event d) (event_measurable d))
  have he := subset_supClosure (rect_mem (left e) (right e) (event e) (event_measurable e))
  have h := mixed_ring_intersection F G hd he
  rw [ringIntegral_rect F _ _ _ (ordered d) (event_measurable d),
    ringIntegral_rect G _ _ _ (ordered e) (event_measurable e)] at h
  exact h

def mixedEnergy (F G : JointL2) (l k : Index →₀ ℝ) : ℝ :=
  ∑ d ∈ l.support, ∑ e ∈ k.support, (l d * k e) *
    covariance F G (rect (left d) (right d) (event d) ∩ rect (left e) (right e) (event e))

theorem finite_mixed_energy (F G : JointL2) (l k : Index →₀ ℝ) :
    inner ℝ (integralLinear F l) (integralLinear G k) = mixedEnergy F G l k := by
  classical
  simp only [integralLinear, Finsupp.linearCombination_apply, Finsupp.sum,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, basis_mixed_energy,
    mixedEnergy, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem mixed_energy_bound (F G : JointL2) (l k : Index →₀ ℝ) :
    |mixedEnergy F G l k| ≤ ‖IBMPredictableLpDictionary.dictionary F l‖ *
      ‖IBMPredictableLpDictionary.dictionary G k‖ := by
  rw [← finite_mixed_energy]
  exact (abs_real_inner_le_norm _ _).trans_eq
    (congrArg₂ (fun a b : ℝ => a*b)
      (IBMPredictableLpDictionary.dictionary_norm F l) (IBMPredictableLpDictionary.dictionary_norm G k))

theorem two_channel_energy (F G : JointL2) (l k : Index →₀ ℝ) :
    ‖integralLinear F l + integralLinear G k‖^2 =
      ‖IBMPredictableLpDictionary.dictionary F l‖^2 +
      2*mixedEnergy F G l k + ‖IBMPredictableLpDictionary.dictionary G k‖^2 := by
  rw [norm_add_sq_real, finite_mixed_energy,
    IBMPredictableLpDictionary.dictionary_norm F l, IBMPredictableLpDictionary.dictionary_norm G k]

theorem finite_family_energy {ι : Type*} (s : Finset ι) (F : ι → JointL2)
    (l : ι → Index →₀ ℝ) :
    ‖∑ i ∈ s, integralLinear (F i) (l i)‖^2 =
      ∑ i ∈ s, ∑ j ∈ s, mixedEnergy (F i) (F j) (l i) (l j) := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [inner_sum, finite_mixed_energy]

theorem mixed_energy_limit (F G : JointL2)
    (a b : ℕ → (Index →₀ ℝ))
    (H : IBMPredictableLpDictionary.PredictableL2 F)
    (K : IBMPredictableLpDictionary.PredictableL2 G)
    (ha : Tendsto (fun n => IBMPredictableLpDictionary.dictionary F (a n)) atTop (𝓝 H))
    (hb : Tendsto (fun n => IBMPredictableLpDictionary.dictionary G (b n)) atTop (𝓝 K)) :
    Tendsto (fun n => mixedEnergy F G (a n) (b n)) atTop
      (𝓝 (inner ℝ (IBMFullPredictableIntegral.integral F H) (IBMFullPredictableIntegral.integral G K))) := by
  have hF := IBMFullPredictableIntegral.integral_limit F a H ha
  have hG := IBMFullPredictableIntegral.integral_limit G b K hb
  simpa only [finite_mixed_energy] using hF.inner (𝕜 := ℝ) hG

end OperatorDerivativeRewrite.Foundation.IBMMixedPredictableEnergy
