import Foundation.IBMCompactPredictableFibers

/-! Compact-fiber inner approximants with controlled actual predictable energy loss. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableCompactApproximation
open IBMPredictableRectangles IBMPredictableRingContent IBMCompactPredictableFibers
open IBMTimeAveragedObservable IBMWeightedTerminalEnergy IBMGermPredictableStep
set_option backward.isDefEq.respectTransparency false

def Approximable (F : JointL2) (E : Set Space) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K D : Set Space, K ∈ compactFinite ∧ K ⊆ E ∧
    D ∈ elementaryRing ∧ E \ K ⊆ D ∧ content F D < ENNReal.ofReal ε

theorem empty_approximable (F : JointL2) : Approximable F ∅ := by
  intro ε hε
  refine ⟨∅, ∅, compact_empty, Subset.rfl, elementary_isSetRing.empty_mem, ?_, ?_⟩
  · exact sdiff_subset
  · rw [addContent_empty]
    exact ENNReal.ofReal_pos.mpr hε

theorem rectangle_approximable (F : JointL2) (s t : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hst : s ≤ t) (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) :
    Approximable F (rect s t A) := by
  rcases hst.eq_or_lt with he | hpos
  · subst t
    simpa only [rect, Ioc_self, empty_prod] using empty_approximable F
  intro ε hε
  let τ := IBMIntrinsicRightApproach.approach s
  have hτ := IBMIntrinsicRightApproach.approach_tendsto s
  have hp := IBMIntrinsicRightApproach.approach_positive s
  have hs : Tendsto (fun n => ‖stepClass F s (τ n) (eventCoefficient s A hA)‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      (IBMGermSupportContinuity.right_trim_tendsto_zero F s (eventCoefficient s A hA)
        τ (fun n => (hp n).le) hτ).norm.pow 2
  obtain ⟨n, hnε, _hnt⟩ := ((hs.eventually (eventually_lt_nhds hε)).and
    (hτ.eventually (eventually_lt_nhds hpos))).exists
  have hd : rect s (τ n) A ∈ elementaryRing := subset_supClosure (rect_mem s (τ n) A hA)
  refine ⟨Icc (τ n) t ×ˢ A, rect s (τ n) A,
    compact_rectangle _ _ isCompact_Icc
      (IBMNaturalFiltrationObstruction.naturalFiltration.le s A hA),
    ?_, hd, ?_, ?_⟩
  · intro p h
    exact ⟨⟨(hp n).trans_le h.1.1, h.1.2⟩, h.2⟩
  · intro p h
    refine ⟨⟨h.1.1.1, ?_⟩, h.1.2⟩
    by_contra hn
    exact h.2 ⟨⟨(lt_of_not_ge hn).le, h.1.1.2⟩, h.1.2⟩
  · rw [content_energy F hd, ringIntegral_rect F s (τ n) A (hp n).le hA]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hnε

theorem union_approximable (F : JointL2) {E H : Set Space}
    (hE : Approximable F E) (hH : Approximable F H) : Approximable F (E ∪ H) := by
  intro ε hε
  obtain ⟨K, D, hK, hKE, hD, hED, hνD⟩ := hE (ε/2) (half_pos hε)
  obtain ⟨L, P, hL, hLH, hP, hHP, hνP⟩ := hH (ε/2) (half_pos hε)
  refine ⟨K ∪ L, D ∪ P, compact_union hK hL, union_subset_union hKE hLH,
    elementary_isSetRing.union_mem hD hP, ?_, ?_⟩
  · rintro p ⟨h, hn⟩
    rcases h with h | h
    · exact Or.inl (hED ⟨h, fun hk => hn (Or.inl hk)⟩)
    · exact Or.inr (hHP ⟨h, fun hl => hn (Or.inr hl)⟩)
  · calc
      content F (D ∪ P) ≤ content F D + content F P :=
        addContent_union_le elementary_isSetRing hD hP
      _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := ENNReal.add_lt_add hνD hνP
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
        congr 1
        ring

theorem ring_approximable (F : JointL2) {E : Set Space} (hE : E ∈ elementaryRing) :
    Approximable F E := by
  have hb : rectangles ⊆ {E | Approximable F E} := by
    rintro E ⟨s, t, A, hst, hA, rfl⟩
    exact rectangle_approximable F s t A hst hA
  have hc : SupClosed {E : Set Space | Approximable F E} := by
    intro E hE H hH
    exact union_approximable F hE hH
  exact supClosure_min hb hc hE

end OperatorDerivativeRewrite.Foundation.IBMPredictableCompactApproximation
