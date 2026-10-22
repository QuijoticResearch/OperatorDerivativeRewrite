import Foundation.IBMWeightedTerminalEnergy

/-! A usual open-closed raw increment-energy measure forces the germ gap to vanish.
This is a necessary condition, not an assertion that the gap is nonzero. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawEnergyMeasureObstruction
open IBMTimeAveragedObservable IBMRawObservedMartingale IBMObservedTerminalMartingale
open IBMIntrinsicRightApproach
set_option backward.isDefEq.respectTransparency false

theorem shrinking_intervals_empty (s : ℝ≥0) : (⋂ n, Ioc s (approach s n)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hs : s < r := (Set.mem_iInter.mp hr 0).1
  have ht : r ≤ s := le_of_tendsto_of_tendsto
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)) (approach_tendsto s)
    (Eventually.of_forall fun n => (Set.mem_iInter.mp hr n).2)
  exact (not_le_of_gt hs) ht

theorem raw_measure_forces_germ_equality (F : JointL2) (s : ℝ≥0) (ν : Measure ℝ≥0)
    (hν : ∀ t, s ≤ t → ν (Ioc s t) =
      ENNReal.ofReal (‖rawClass F t - rawClass F s‖ ^ 2)) :
    channelClass F s = rawClass F s := by
  have hm := tendsto_measure_iInter_atTop (μ := ν)
    (s := fun n => Ioc s (approach s n))
    (fun _ => measurableSet_Ioc.nullMeasurableSet)
    (fun i j hij => Ioc_subset_Ioc_right (approach_antitone s hij)) (by
      refine ⟨0, ?_⟩
      rw [hν _ (approach_positive s 0).le]
      exact ENNReal.ofReal_ne_top)
  rw [shrinking_intervals_empty, measure_empty] at hm
  have hg := ENNReal.tendsto_ofReal (((raw_right_limit F (approach s)
    (approach_antitone s) s (approach_positive s) (approach_tendsto s)).sub_const
      (rawClass F s)).norm.pow 2)
  have hz : ENNReal.ofReal (‖channelClass F s - rawClass F s‖ ^ 2) = 0 := by
    apply tendsto_nhds_unique hg
    have he (n : ℕ) := hν (approach s n) (approach_positive s n).le
    change Tendsto (fun n => ν (Ioc s (approach s n))) atTop (𝓝 0) at hm
    exact Filter.Tendsto.congr' (Eventually.of_forall he) hm
  have hn := ENNReal.ofReal_eq_zero.mp hz
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (channelClass F s - rawClass F s)]

theorem no_raw_measure_of_germ_gap (F : JointL2) (s : ℝ≥0)
    (hgap : channelClass F s ≠ rawClass F s) :
    ¬∃ ν : Measure ℝ≥0, ∀ t, s ≤ t → ν (Ioc s t) =
      ENNReal.ofReal (‖rawClass F t - rawClass F s‖ ^ 2) := by
  rintro ⟨ν, hν⟩
  exact hgap (raw_measure_forces_germ_equality F s ν hν)

theorem finite_raw_energy_measure_iff (F : JointL2) :
    (∃ ν : Measure ℝ≥0, IsFiniteMeasure ν ∧ ∀ s t, s ≤ t → ν (Ioc s t) =
      ENNReal.ofReal (‖rawClass F t - rawClass F s‖ ^ 2)) ↔
        ∀ s, channelClass F s = rawClass F s := by
  constructor
  · rintro ⟨ν, _, hν⟩ s
    exact raw_measure_forces_germ_equality F s ν (hν s)
  · intro hg
    refine ⟨IBMTerminalEnergyMeasure.energyMeasure F, IBMTerminalEnergyMeasure.finite_measure F, ?_⟩
    intro s t hst
    rw [IBMTerminalEnergyMeasure.energyMeasure_increment F hst, hg s, hg t]

end OperatorDerivativeRewrite.Foundation.IBMRawEnergyMeasureObstruction
