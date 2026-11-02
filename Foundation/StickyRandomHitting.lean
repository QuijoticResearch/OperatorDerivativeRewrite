import Foundation.StickyHittingRestart
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-! Random-start continuous hitting windows and native sticky splicing.
Random-time substitution uses a single all-window AE event, not per-window AE. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyRandomHitting
open InfiniteGaussian IBMConstructedSources BrownianMassClockStoppingTime
open StickyHittingRestart

variable {Ω : Type*} [m : MeasurableSpace Ω]

theorem truncated_stop_measurable (ℱ : Filtration ℝ≥0 m) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) (t : ℝ≥0) :
    Measurable[ℱ t] (fun ω => min (τ ω) t) := by
  have ht := (hτ.min_const t).measurable_of_le (fun ω => min_le_right _ _)
  have hu := ht.untopD (0 : ℝ≥0)
  simpa only [← WithTop.coe_min, WithTop.untopD_coe] using hu

/-- A variable lower endpoint is retained in a closed compact-prefix event. -/
theorem zeroAfter_closed (t : ℝ≥0) :
    IsClosed {z : ℝ≥0 × C(Icc (0 : ℝ≥0) t, ℝ) |
      ∃ r : Icc (0 : ℝ≥0) t, z.1 ≤ r ∧ z.2 r = 0} := by
  have hc : IsClosed {z : (ℝ≥0 × C(Icc (0 : ℝ≥0) t, ℝ)) × Icc (0 : ℝ≥0) t |
      z.1.1 ≤ z.2 ∧ z.1.2 z.2 = 0} :=
    (isClosed_le continuous_fst.fst continuous_snd.subtype_val).inter
      (isClosed_eq (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)) continuous_const)
  have hh := isClosedMap_fst_of_compactSpace _ hc
  convert hh using 1
  ext z
  simp

def randomHit (p : Ω → C(ℝ≥0, ℝ)) (τ : Ω → ℝ≥0) (h : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  hit (p ω) (τ ω) (τ ω+h)

theorem randomHit_stopping (ℱ : Filtration ℝ≥0 m) (p : Ω → C(ℝ≥0, ℝ))
    (hp : ∀ r, Measurable[ℱ r] (fun ω => p ω r)) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) (h : ℝ≥0) :
    IsStoppingTime ℱ (fun ω => (randomHit p τ h ω : WithTop ℝ≥0)) := by
  intro t
  let K : Ω → ℝ≥0 × C(Icc (0 : ℝ≥0) t, ℝ) :=
    fun ω => (min (τ ω) t, windowPath (p ω) 0 t)
  have hK : Measurable[ℱ t] K :=
    (truncated_stop_measurable ℱ τ hτ t).prodMk (windowPath_measurable ℱ p hp 0 t)
  have hstart : MeasurableSet[ℱ t] {ω | τ ω ≤ t} := by
    simpa only [WithTop.coe_le_coe] using hτ t
  have hend : MeasurableSet[ℱ t] {ω | τ ω+h ≤ t} := by
    simpa only [WithTop.coe_le_coe] using BrownianStoppedFourier.delay_isStoppingTime ℱ τ hτ h t
  have he : {ω | (randomHit p τ h ω : WithTop ℝ≥0) ≤ t} =
      {ω | τ ω+h ≤ t} ∪ ({ω | τ ω ≤ t} ∩ K ⁻¹'
        {z | ∃ r : Icc (0 : ℝ≥0) t, z.1 ≤ r ∧ z.2 r = 0}) := by
    ext ω
    simp only [mem_setOf_eq, mem_union, mem_inter_iff, mem_preimage, WithTop.coe_le_coe]
    change hit (p ω) (τ ω) (τ ω+h) ≤ t ↔
      τ ω+h ≤ t ∨ (τ ω ≤ t ∧
        ∃ r : Icc (0 : ℝ≥0) t, min (τ ω) t ≤ r ∧ p ω r = 0)
    by_cases hc : τ ω+h ≤ t
    · exact ⟨fun _ => Or.inl hc, fun _ => (hit_le _ _ _).trans hc⟩
    · rw [hit_le_iff _ _ _ _ (lt_of_not_ge hc)]
      constructor
      · rintro ⟨r, hr, hz⟩
        have ha := hr.1.trans hr.2
        exact Or.inr ⟨ha, ⟨⟨r, bot_le, hr.2⟩, by simpa [min_eq_left ha] using hr.1, hz⟩⟩
      · rintro (hend | ⟨ha, r, hr, hz⟩)
        · exact (hc hend).elim
        · exact ⟨r, ⟨by simpa [min_eq_left ha] using hr, r.property.2⟩, hz⟩
  rw [he]
  exact hend.union (hstart.inter ((zeroAfter_closed t).measurableSet.preimage hK))

/-- ONE original good event covers all deterministic windows before ANY
random starting time is substituted. -/
theorem all_window_mass : ∀ᵐ ω ∂gaussianProduct, ∀ a T : ℝ≥0,
    ∀ r ∈ Icc a (hit (clockPath ω) a T),
      BrownianRandomMassClock.mass ω r = BrownianRandomMassClock.mass ω a := by
  filter_upwards [BrownianMassZeroFreeIntervals.zero_free_constant,
    BrownianRandomMassClock.mass_agrees] with ω hz hm a T r hr
  have hi : Ico a (hit (clockPath ω) a T) ⊆
      {r | BrownianRandomMassClock.mass ω r = BrownianRandomMassClock.mass ω a} := by
    intro v hv
    have hn : ∀ u ∈ Icc a v, clockPath ω u ≠ 0 := fun u hu =>
      zero_free_before (clockPath ω) a T u hu.1 (hu.2.trans_lt hv.2)
    have he := hz a v hv.1 hn
    apply NNReal.coe_injective
    rw [hm v, hm a]
    exact he.symm
  by_cases hEq : a = hit (clockPath ω) a T
  · have he : r = a := le_antisymm (hr.2.trans_eq hEq.symm) hr.1
    rw [he]
  · have hc : IsClosed {r | BrownianRandomMassClock.mass ω r =
        BrownianRandomMassClock.mass ω a} :=
      isClosed_eq (BrownianRandomMassClock.mass_continuous ω) continuous_const
    have hfull := closure_minimal hi hc
    rw [closure_Ico hEq] at hfull
    exact hfull hr

theorem random_clock_prehit (κ : ℝ≥0) (τ : SampleSpace → ℝ≥0) (h : ℝ≥0) :
    ∀ᵐ ω ∂gaussianProduct, ∀ r ∈ Icc (τ ω) (randomHit clockPath τ h ω),
      BrownianRandomMassClock.forward κ ω r =
        BrownianRandomMassClock.forward κ ω (τ ω)+(r-τ ω) := by
  filter_upwards [all_window_mass] with ω hm r hr
  dsimp only [BrownianRandomMassClock.forward, StickyTimeChangeClock.clock]
  rw [hm (τ ω) (τ ω+h) r hr]
  calc
    _ = (τ ω+(r-τ ω)) + κ * BrownianRandomMassClock.mass ω (τ ω) := by
      rw [add_tsub_cancel_of_le hr.1]
    _ = _ := by ring

theorem random_prehit (κ : ℝ≥0) (τ : SampleSpace → ℝ≥0) (h : ℝ≥0) :
    ∀ᵐ ω ∂gaussianProduct, ∀ r ∈ Icc (τ ω) (randomHit clockPath τ h ω),
      BrownianMassRandomTimeChange.changedPath κ ω
        (BrownianRandomMassClock.forward κ ω (τ ω)+(r-τ ω)) = clockPath ω r := by
  filter_upwards [random_clock_prehit κ τ h] with ω hm r hr
  rw [← hm r hr]
  exact BrownianMassRandomTimeChange.recover_original κ ω r

theorem random_posthit (κ : ℝ≥0) (τ : SampleSpace → ℝ≥0)
    (hτ : IsStoppingTime augmentedPast (fun ω => (τ ω : WithTop ℝ≥0))) (h : ℝ≥0) :
    ∀ᵐ ω ∂gaussianProduct, randomHit clockPath τ h ω < τ ω+h → ∀ u : ℝ≥0,
      BrownianMassRandomTimeChange.changedPath κ ω
        (BrownianRandomMassClock.forward κ ω (randomHit clockPath τ h ω)+u) =
        StickyRestartRealization.restartedSticky κ (randomHit clockPath τ h) ω u := by
  have hstop := randomHit_stopping augmentedPast clockPath
    (fun r => (BrownianAugmentedMartingales.brownian_stronglyAdapted r).measurable) τ hτ h
  filter_upwards [stopped_boundary_restart κ (randomHit clockPath τ h) hstop] with ω hω ht
  exact hω (hit_zero_of_lt (clockPath ω) (τ ω) (τ ω+h) ht)

/-- The actual random start needed at a deterministic PHYSICAL observation. -/
theorem inverse_clock_prehit (κ s h : ℝ≥0) : ∀ᵐ ω ∂gaussianProduct,
    ∀ r ∈ Icc (BrownianMassRandomTimeChange.inverse κ ω s)
      (randomHit clockPath (fun w => BrownianMassRandomTimeChange.inverse κ w s) h ω),
      BrownianMassRandomTimeChange.changedPath κ ω
        (s+(r-BrownianMassRandomTimeChange.inverse κ ω s)) = clockPath ω r := by
  filter_upwards [random_prehit κ (fun w => BrownianMassRandomTimeChange.inverse κ w s) h]
    with ω hω r hr
  have he := hω r hr
  rwa [BrownianMassRandomTimeChange.forward_inverse] at he

/-- The post-hit physical time is expressed relative to the actual observation
s, not hidden behind an operational forward clock. -/
theorem inverse_clock_posthit (κ s h : ℝ≥0) : ∀ᵐ ω ∂gaussianProduct,
    randomHit clockPath (fun w => BrownianMassRandomTimeChange.inverse κ w s) h ω <
      BrownianMassRandomTimeChange.inverse κ ω s+h → ∀ u : ℝ≥0,
      BrownianMassRandomTimeChange.changedPath κ ω
        (s+(randomHit clockPath (fun w => BrownianMassRandomTimeChange.inverse κ w s) h ω -
          BrownianMassRandomTimeChange.inverse κ ω s)+u) =
        StickyRestartRealization.restartedSticky κ
          (randomHit clockPath (fun w => BrownianMassRandomTimeChange.inverse κ w s) h) ω u := by
  let τ : SampleSpace → ℝ≥0 := fun w => BrownianMassRandomTimeChange.inverse κ w s
  have hτ := inverse_isStoppingTime κ s
  filter_upwards [random_posthit κ τ hτ h, random_clock_prehit κ τ h] with ω hp hc ht u
  have hle : τ ω ≤ randomHit clockPath τ h ω :=
    le_hit (clockPath ω) (τ ω) (τ ω+h) (le_add_right le_rfl)
  have he := hp ht u
  rw [hc _ ⟨hle, le_rfl⟩, BrownianMassRandomTimeChange.forward_inverse] at he
  exact he

end OperatorDerivativeRewrite.Foundation.StickyRandomHitting
