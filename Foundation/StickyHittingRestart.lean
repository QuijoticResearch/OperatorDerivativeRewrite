import Foundation.StickyBoundaryRestart
import Foundation.BrownianAugmentedMartingales
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Maps.Proper.Basic

/-! Continuous bounded hitting windows needed for actual sticky restart.
The existing hittingBtwn is reused; no discrete-time stopping lemma is applied. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyHittingRestart
open InfiniteGaussian IBMConstructedSources BrownianMassClockStoppingTime
open StickyBoundaryRestart

def hit (p : C(ℝ≥0, ℝ)) (a T : ℝ≥0) : ℝ≥0 :=
  hittingBtwn (fun t (q : C(ℝ≥0, ℝ)) => q t) {0} a T p

theorem hit_le (p : C(ℝ≥0, ℝ)) (a T : ℝ≥0) : hit p a T ≤ T := hittingBtwn_le p

theorem le_hit (p : C(ℝ≥0, ℝ)) (a T : ℝ≥0) (haT : a ≤ T) : a ≤ hit p a T :=
  le_hittingBtwn haT p

theorem hit_zero_of_exists (p : C(ℝ≥0, ℝ)) (a T : ℝ≥0)
    (he : ∃ t ∈ Icc a T, p t = 0) : p (hit p a T) = 0 := by
  have hne : (Icc a T ∩ {t | p t = 0}).Nonempty := by
    obtain ⟨t, ht, hz⟩ := he
    exact ⟨t, ht, hz⟩
  have hc : IsCompact (Icc a T ∩ {t | p t = 0}) :=
    isCompact_Icc.inter_right (isClosed_eq p.continuous continuous_const)
  have hm := hc.sInf_mem hne
  have hx : ∃ t ∈ Icc a T, p t ∈ ({0} : Set ℝ) := by simpa using he
  simpa only [hit, hittingBtwn, if_pos hx, mem_singleton_iff, mem_setOf_eq] using hm.2

theorem hit_zero_of_lt (p : C(ℝ≥0, ℝ)) (a T : ℝ≥0) (ht : hit p a T < T) :
    p (hit p a T) = 0 := by
  by_cases he : ∃ t ∈ Icc a T, p t = 0
  · exact hit_zero_of_exists p a T he
  · have hn : ¬ ∃ t ∈ Icc a T, p t ∈ ({0} : Set ℝ) := by simpa using he
    have hh : hit p a T = T := by simp only [hit, hittingBtwn, if_neg hn]
    rw [hh] at ht
    exact (lt_irrefl _ ht).elim

theorem zero_free_before (p : C(ℝ≥0, ℝ)) (a T t : ℝ≥0)
    (hat : a ≤ t) (ht : t < hit p a T) : p t ≠ 0 := by
  have h := notMem_of_lt_hittingBtwn ht hat
  simpa using h

theorem hit_le_iff (p : C(ℝ≥0, ℝ)) (a T t : ℝ≥0) (ht : t < T) :
    hit p a T ≤ t ↔ ∃ r ∈ Icc a t, p r = 0 := by
  constructor
  · intro h
    have hz := hit_zero_of_lt p a T (h.trans_lt ht)
    have he : ∃ r ∈ Icc a T, p r = 0 := by
      by_contra hn
      have hn' : ¬ ∃ r ∈ Icc a T, p r ∈ ({0} : Set ℝ) := by simpa using hn
      have hh : hit p a T = T := by simp only [hit, hittingBtwn, if_neg hn']
      rw [hh] at h
      exact (not_le_of_gt ht) h
    obtain ⟨r, hr, _⟩ := he
    exact ⟨hit p a T, ⟨le_hit p a T (hr.1.trans hr.2), h⟩, hz⟩
  · rintro ⟨r, hr, hz⟩
    have h := hittingBtwn_le_of_mem
      (u := fun t (q : C(ℝ≥0, ℝ)) => q t) (s := ({0} : Set ℝ))
      (n := a) (m := T) (ω := p) hr.1 (hr.2.trans ht.le)
      (show p r ∈ ({0} : Set ℝ) from hz)
    exact h.trans hr.2

def windowPath (p : C(ℝ≥0, ℝ)) (a t : ℝ≥0) : C(Icc a t, ℝ) :=
  p.comp ⟨Subtype.val, continuous_subtype_val⟩

theorem zero_prefix_closed (a t : ℝ≥0) :
    IsClosed {q : C(Icc a t, ℝ) | ∃ r, q r = 0} := by
  have hc : IsClosed {z : C(Icc a t, ℝ) × Icc a t | z.1 z.2 = 0} :=
    isClosed_eq continuous_eval continuous_const
  have h := isClosedMap_fst_of_compactSpace _ hc
  convert h using 1
  ext q
  simp

variable {Ω : Type*} [m : MeasurableSpace Ω]

theorem windowPath_measurable (ℱ : Filtration ℝ≥0 m) (p : Ω → C(ℝ≥0, ℝ))
    (hp : ∀ r, Measurable[ℱ r] (fun ω => p ω r)) (a t : ℝ≥0) :
    Measurable[ℱ t] (fun ω => windowPath (p ω) a t) := by
  letI : MeasurableSpace Ω := ℱ t
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  exact (hp r).mono (ℱ.mono r.property.2) le_rfl

/-- A continuous adapted path's bounded closed-level hitting window is an
actual stopping time, without countable or well-founded continuous time. -/
theorem hit_isStoppingTime (ℱ : Filtration ℝ≥0 m) (p : Ω → C(ℝ≥0, ℝ))
    (hp : ∀ r, Measurable[ℱ r] (fun ω => p ω r)) (a T : ℝ≥0) :
    IsStoppingTime ℱ (fun ω => (hit (p ω) a T : WithTop ℝ≥0)) := by
  intro t
  by_cases hT : T ≤ t
  · have he : {ω | (hit (p ω) a T : WithTop ℝ≥0) ≤ t} = univ := by
      ext ω
      simp only [mem_setOf_eq, WithTop.coe_le_coe, mem_univ, iff_true]
      exact (hit_le (p ω) a T).trans hT
    rw [he]
    exact MeasurableSet.univ
  · have he : {ω | (hit (p ω) a T : WithTop ℝ≥0) ≤ t} =
        (fun ω => windowPath (p ω) a t) ⁻¹' {q | ∃ r, q r = 0} := by
      ext ω
      simp only [mem_setOf_eq, WithTop.coe_le_coe, mem_preimage, hit_le_iff _ _ _ _ (lt_of_not_ge hT)]
      constructor
      · rintro ⟨r, hr, hz⟩
        exact ⟨⟨r, hr⟩, hz⟩
      · rintro ⟨r, hr⟩
        exact ⟨r, r.property, hr⟩
    rw [he]
    exact (zero_prefix_closed a t).measurableSet.preimage (windowPath_measurable ℱ p hp a t)

/-- Native whole-path physical restart at ANY supplied finite operational stop
on its zero event. This strengthens fixed physical-time boundary restart. -/
theorem stopped_boundary_restart (κ : ℝ≥0) (τ : SampleSpace → ℝ≥0)
    (hτ : IsStoppingTime augmentedPast (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂gaussianProduct, clockPath ω (τ ω) = 0 → ∀ u : ℝ≥0,
      BrownianMassRandomTimeChange.changedPath κ ω (BrownianRandomMassClock.forward κ ω (τ ω)+u) =
        StickyRestartRealization.restartedSticky κ τ ω u := by
  filter_upwards [original_good, restarted_good τ hτ,
    StickyWienerPathRealization.mass_agrees, StickyWienerPathRealization.stickyPath_agrees]
    with ω hp hr hm hpath hz u
  have hs : Good (shift (clockPath ω) (τ ω)) := hr
  have he := sticky_shift κ (clockPath ω) (τ ω) u hp hs hz
  rw [hm, hpath κ] at he
  exact he

def brownianHit (a T : ℝ≥0) (ω : SampleSpace) : ℝ≥0 := hit (clockPath ω) a T

theorem brownianHit_stopping (a T : ℝ≥0) :
    IsStoppingTime augmentedPast (fun ω => (brownianHit a T ω : WithTop ℝ≥0)) :=
  hit_isStoppingTime augmentedPast clockPath
    (fun r => (BrownianAugmentedMartingales.brownian_stronglyAdapted r).measurable) a T

/-- First-hit physical continuation of the ORIGINAL stochastic time change.
The stop is finite even when no zero occurs; the event hit<T supplies a zero. -/
theorem first_hit_restart (κ a T : ℝ≥0) : ∀ᵐ ω ∂gaussianProduct,
    brownianHit a T ω < T → ∀ u : ℝ≥0,
      BrownianMassRandomTimeChange.changedPath κ ω
        (BrownianRandomMassClock.forward κ ω (brownianHit a T ω)+u) =
        StickyRestartRealization.restartedSticky κ (brownianHit a T) ω u := by
  filter_upwards [stopped_boundary_restart κ (brownianHit a T) (brownianHit_stopping a T)]
    with ω hω ht
  exact hω (hit_zero_of_lt (clockPath ω) a T ht)

/-- No accumulated sticky mass before the first boundary hit, including the
hitting endpoint by continuity. All operational times share one AE event. -/
theorem mass_constant_until_hit (a T : ℝ≥0) (haT : a ≤ T) : ∀ᵐ ω ∂gaussianProduct,
    ∀ r ∈ Icc a (brownianHit a T ω),
      BrownianRandomMassClock.mass ω r = BrownianRandomMassClock.mass ω a := by
  filter_upwards [BrownianMassZeroFreeIntervals.zero_free_constant,
    BrownianRandomMassClock.mass_agrees] with ω hz hm
  have hi : Ico a (brownianHit a T ω) ⊆
      {r | BrownianRandomMassClock.mass ω r = BrownianRandomMassClock.mass ω a} := by
    intro r hr
    have hn : ∀ u ∈ Icc a r, clockPath ω u ≠ 0 := fun u hu =>
      zero_free_before (clockPath ω) a T u hu.1 (hu.2.trans_lt hr.2)
    have he := hz a r hr.1 hn
    apply NNReal.coe_injective
    rw [hm r, hm a]
    exact he.symm
  intro r hr
  by_cases hEq : a = brownianHit a T ω
  · have he : r = a := le_antisymm (hr.2.trans_eq hEq.symm) hr.1
    rw [he]
  · have hc : IsClosed {r | BrownianRandomMassClock.mass ω r =
        BrownianRandomMassClock.mass ω a} :=
      isClosed_eq (BrownianRandomMassClock.mass_continuous ω) continuous_const
    have hfull := closure_minimal hi hc
    rw [closure_Ico hEq] at hfull
    exact hfull hr

/-- Exact actual physical trajectory before the first hit, not only an
expectation or clock bound: the path follows its original Brownian segment. -/
theorem physical_before_hit (κ a T : ℝ≥0) (haT : a ≤ T) : ∀ᵐ ω ∂gaussianProduct,
    ∀ r ∈ Icc a (brownianHit a T ω),
      BrownianMassRandomTimeChange.changedPath κ ω
        (BrownianRandomMassClock.forward κ ω a + (r-a)) = clockPath ω r := by
  filter_upwards [mass_constant_until_hit a T haT] with ω hm r hr
  have hf : BrownianRandomMassClock.forward κ ω r =
      BrownianRandomMassClock.forward κ ω a + (r-a) := by
    dsimp only [BrownianRandomMassClock.forward, StickyTimeChangeClock.clock]
    rw [hm r hr]
    calc
      _ = (a+(r-a)) + κ * BrownianRandomMassClock.mass ω a := by
        rw [add_tsub_cancel_of_le hr.1]
      _ = _ := by ring
  rw [← hf]
  exact BrownianMassRandomTimeChange.recover_original κ ω r

end OperatorDerivativeRewrite.Foundation.StickyHittingRestart
