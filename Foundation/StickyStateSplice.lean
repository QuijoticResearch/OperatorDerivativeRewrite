import Foundation.StickyRandomHitting
import Foundation.IndependentInnovationConditioning

/-! Borel current-state/Wiener-path splicing for the original sticky time change.
No conditional law, full Markov property or spatial Green domain is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyStateSplice
open InfiniteGaussian IBMConstructedSources BrownianMassClockStoppingTime
open StickyHittingRestart StickyBoundaryRestart StickyRandomHitting

abbrev Path := C(ℝ≥0, ℝ)

def offset (x : ℝ) (p : Path) : Path := ContinuousMap.const _ x + p

theorem offset_continuous : Continuous (fun z : ℝ × Path => offset z.1 z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (ℝ × Path) × ℝ≥0 => z.1.1 + z.1.2 z.2)
  exact continuous_fst.fst.add (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd))

theorem shift_continuous : Continuous (fun z : Path × ℝ≥0 => shift z.1 z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (Path × ℝ≥0) × ℝ≥0 => z.1.1 (z.1.2+z.2)-z.1.1 z.1.2)
  exact (continuous_eval.comp (continuous_fst.fst.prodMk
    (continuous_fst.snd.add continuous_snd))).sub
      (continuous_eval.comp (continuous_fst.fst.prodMk continuous_fst.snd))

def hitTime (h : ℝ≥0) (x : ℝ) (p : Path) : ℝ≥0 := hit (offset x p) 0 h

theorem hitTime_le (h : ℝ≥0) (x : ℝ) (p : Path) : hitTime h x p ≤ h := hit_le _ _ _

theorem hitTime_measurable (h : ℝ≥0) : Measurable (fun z : ℝ × Path => hitTime h z.1 z.2) := by
  let ℱ : Filtration ℝ≥0 (Prod.instMeasurableSpace : MeasurableSpace (ℝ × Path)) :=
    Filtration.const ℝ≥0 (Prod.instMeasurableSpace : MeasurableSpace (ℝ × Path)) le_rfl
  have hp (r : ℝ≥0) : Measurable[ℱ r] (fun z : ℝ × Path => offset z.1 z.2 r) :=
    (ContinuousMap.measurable_eval r).comp offset_continuous.measurable
  have ht := hit_isStoppingTime ℱ (fun z : ℝ × Path => offset z.1 z.2) hp 0 h
  have hm := ht.measurable_of_le (fun z =>
    WithTop.coe_le_coe.mpr (hit_le (offset z.1 z.2) 0 h))
  have hu := (hm.untopD (0 : ℝ≥0)).mono (ℱ.le h) le_rfl
  simpa only [hitTime, WithTop.untopD_coe] using hu

/-- A total Borel map. The no-hit/endpoint-hit branch includes zero horizon. -/
def value (κ h : ℝ≥0) (x : ℝ) (p : Path) : ℝ :=
  if hitTime h x p < h then
    StickyWienerPathRealization.stickyPath κ (shift p (hitTime h x p)) (h-hitTime h x p)
  else x+p h

theorem value_measurable (κ h : ℝ≥0) : Measurable (fun z : ℝ × Path => value κ h z.1 z.2) := by
  have ht := hitTime_measurable h
  have hs : Measurable (fun z : ℝ × Path => shift z.2 (hitTime h z.1 z.2)) :=
    shift_continuous.measurable.comp (measurable_snd.prodMk ht)
  have hc : Measurable (fun z : ℝ × Path =>
      StickyWienerPathRealization.stickyPath κ (shift z.2 (hitTime h z.1 z.2))) :=
    (StickyWienerPathRealization.stickyPath_measurable κ).comp hs
  have hev : Measurable (fun z : Path × ℝ≥0 => z.1 z.2) := continuous_eval.measurable
  exact Measurable.ite (measurableSet_lt ht measurable_const)
    (hev.comp (hc.prodMk (measurable_const.sub ht)))
    (measurable_fst.add ((ContinuousMap.measurable_eval h).comp measurable_snd))

theorem offset_shift (p : Path) (a t : ℝ≥0) : offset (p a) (shift p a) t = p (a+t) := by
  change p a+(p (a+t)-p a) = _
  ring

theorem shift_shift (p : Path) (a b : ℝ≥0) : shift (shift p a) b = shift p (a+b) := by
  ext t
  simp only [shift, ContinuousMap.coe_mk, add_assoc]
  ring

/-- Exact translation of the first-hit window; no probability or Good-path
assumption is used in this deterministic continuous-path identity. -/
theorem hit_translate (p : Path) (a h : ℝ≥0) :
    hit p a (a+h) = a+hitTime h (p a) (shift p a) := by
  have hlo := le_hit p a (a+h) (le_add_right le_rfl)
  have hhi := hit_le p a (a+h)
  have hs := hitTime_le h (p a) (shift p a)
  apply le_antisymm
  · by_cases he : hitTime h (p a) (shift p a) = h
    · rw [he]; exact hhi
    · have hlt := lt_of_le_of_ne hs he
      have hz := hit_zero_of_lt (offset (p a) (shift p a)) 0 h hlt
      rw [offset_shift] at hz
      exact (hit_le_iff p a (a+h) _ (add_lt_add_of_le_of_lt (le_refl a) hlt)).mpr
        ⟨_, ⟨le_add_right le_rfl, le_rfl⟩, hz⟩
  · by_contra hn
    have hb : hit p a (a+h) < a+hitTime h (p a) (shift p a) := lt_of_not_ge hn
    have hT : hit p a (a+h) < a+h := hb.trans_le (add_le_add (le_refl a) hs)
    have hz := hit_zero_of_lt p a (a+h) hT
    have hr : hit p a (a+h)-a < hitTime h (p a) (shift p a) := by
      apply (add_lt_add_iff_left a).mp
      rwa [add_tsub_cancel_of_le hlo]
    have hfree := zero_free_before (offset (p a) (shift p a)) 0 h
      (hit p a (a+h)-a) bot_le hr
    apply hfree
    rw [offset_shift, add_tsub_cancel_of_le hlo]
    exact hz

/-- Actual current-state/whole-Brownian-innovation representation of the
original scalar sticky process at every fixed deterministic physical step. -/
theorem native_representation (κ s h : ℝ≥0) : ∀ᵐ ω ∂gaussianProduct,
    BrownianMassRandomTimeChange.changedPath κ ω (s+h) =
      value κ h (BrownianMassRandomTimeChange.changedPath κ ω s)
        (BrownianBoundedRestartProcess.path
          (fun w => BrownianMassRandomTimeChange.inverse κ w s) ω) := by
  let τ : SampleSpace → ℝ≥0 := fun w => BrownianMassRandomTimeChange.inverse κ w s
  let H := randomHit clockPath τ h
  filter_upwards [inverse_clock_prehit κ s h, inverse_clock_posthit κ s h] with ω hpre hpost
  let R : Path := BrownianBoundedRestartProcess.path τ ω
  let σ := hitTime h (BrownianMassRandomTimeChange.changedPath κ ω s) R
  have hH : H ω = τ ω+σ := hit_translate (clockPath ω) (τ ω) h
  have hs : σ ≤ h := hitTime_le h _ R
  change BrownianMassRandomTimeChange.changedPath κ ω (s+h) =
    if σ < h then StickyWienerPathRealization.stickyPath κ (shift R σ) (h-σ)
    else BrownianMassRandomTimeChange.changedPath κ ω s+R h
  by_cases hc : σ < h
  · rw [if_pos hc]
    have hlt : H ω < τ ω+h := by
      rw [hH]
      exact add_lt_add_of_le_of_lt le_rfl hc
    have hp := hpost hlt (h-σ)
    have hpath : BrownianBoundedRestartProcess.path H ω = shift R σ := by
      change shift (clockPath ω) (H ω) = shift (shift (clockPath ω) (τ ω)) σ
      rw [shift_shift, hH]
    change BrownianMassRandomTimeChange.changedPath κ ω (s+(H ω-τ ω)+(h-σ)) =
      StickyWienerPathRealization.stickyPath κ (BrownianBoundedRestartProcess.path H ω) (h-σ) at hp
    rw [hpath] at hp
    have ht : s+(H ω-τ ω)+(h-σ) = s+h := by
      rw [hH, add_tsub_cancel_left, add_assoc, add_tsub_cancel_of_le hc.le]
    rwa [ht] at hp
  · rw [if_neg hc]
    have he : σ = h := le_antisymm hs (le_of_not_gt hc)
    have hmem : τ ω+h ∈ Icc (τ ω) (H ω) := by
      rw [hH, he]
      exact ⟨le_add_right le_rfl, le_rfl⟩
    have hp := hpre (τ ω+h) hmem
    have hb : BrownianMassRandomTimeChange.changedPath κ ω (s+h) = clockPath ω (τ ω+h) := by
      simpa only [τ, add_tsub_cancel_left] using hp
    rw [hb]
    change clockPath ω (τ ω+h) = clockPath ω (τ ω)+(clockPath ω (τ ω+h)-clockPath ω (τ ω))
    ring

def past (κ s : ℝ≥0) : SampleSpace → (Iic s → ℝ) :=
  GaussianPredictableStep.pastProcess (fun t ω => BrownianMassRandomTimeChange.changedPath κ ω t) s

theorem past_measurable (κ s : ℝ≥0) : Measurable (past κ s) :=
  measurable_pi_iff.mpr (fun r => BrownianMassRandomTimeChange.changedPath_coordinate_measurable κ r)

theorem history_eq_comap (κ s : ℝ≥0) :
    StickyNaturalClock.naturalPast κ s = MeasurableSpace.comap (past κ s) inferInstance := by
  rw [StickyNaturalClock.naturalPast, Filtration.natural_eq_comap]
  rfl

/-- The entire original observed history is independent of the whole Brownian
innovation after its endogenous inverse clock. -/
theorem past_innovation_independent (κ s : ℝ≥0) :
    IndepFun (past κ s) (BrownianBoundedRestartProcess.path
      (fun w => BrownianMassRandomTimeChange.inverse κ w s)) gaussianProduct := by
  have hi := BrownianFiniteStrongMarkov.path_independent
    (fun w => BrownianMassRandomTimeChange.inverse κ w s) (inverse_isStoppingTime κ s)
  have hsub : MeasurableSpace.comap (past κ s) inferInstance ≤
      (inverse_isStoppingTime κ s).measurableSpace := by
    rw [← history_eq_comap]
    exact StickyNaturalMartingales.natural_le_physical κ s
  exact indep_of_indep_of_le_left hi.symm hsub

/-- Native deterministic-time transition conditioning on the ENTIRE observed
history. Bounded Borel observables are explicit; no PRP is assumed. -/
theorem conditional_raw (κ s h : ℝ≥0) (f : ℝ → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : ∀ x, ‖f x‖ ≤ M) :
    gaussianProduct[(fun ω => f (BrownianMassRandomTimeChange.changedPath κ ω (s+h))) |
      StickyNaturalClock.naturalPast κ s] =ᵐ[gaussianProduct]
    (fun ω => ∫ p, f (value κ h (BrownianMassRandomTimeChange.changedPath κ ω s) p)
      ∂gaussianProduct.map clockPath) := by
  let τ : SampleSpace → ℝ≥0 := fun w => BrownianMassRandomTimeChange.inverse κ w s
  let F : (Iic s → ℝ) × Path → ℝ := fun z => f (value κ h (z.1 ⟨s, by simp⟩) z.2)
  have hEval : Measurable (fun z : (Iic s → ℝ) × Path => z.1 ⟨s, by simp⟩) :=
    (measurable_pi_apply (⟨s, by simp⟩ : Iic s)).comp measurable_fst
  have hPair : Measurable (fun z : (Iic s → ℝ) × Path => (z.1 ⟨s, by simp⟩, z.2)) :=
    hEval.prodMk measurable_snd
  have hValue : Measurable (fun z : (Iic s → ℝ) × Path =>
      value κ h (z.1 ⟨s, by simp⟩) z.2) := (value_measurable κ h).comp hPair
  have hF : Measurable F := hf.comp hValue
  have hi : Integrable (fun ω => f (BrownianMassRandomTimeChange.changedPath κ ω (s+h)))
      gaussianProduct := Integrable.of_bound
    (hf.comp (BrownianMassRandomTimeChange.changedPath_coordinate_measurable κ (s+h))).aestronglyMeasurable
    M (Eventually.of_forall (fun ω => hM _))
  have he : (fun ω => F (past κ s ω, BrownianBoundedRestartProcess.path τ ω)) =ᵐ[gaussianProduct]
      (fun ω => f (BrownianMassRandomTimeChange.changedPath κ ω (s+h))) := by
    filter_upwards [native_representation κ s h] with ω hω
    exact congrArg f hω.symm
  have hc := IndependentInnovationConditioning.conditional_integral gaussianProduct
    (past κ s) (BrownianBoundedRestartProcess.path τ) (past_measurable κ s)
    (BrownianBoundedRestartProcess.path_measurable τ (inverse_isStoppingTime κ s))
    (past_innovation_independent κ s) F hF.stronglyMeasurable (hi.congr he.symm)
  rw [← history_eq_comap κ s, BrownianFiniteStrongMarkov.path_law τ (inverse_isStoppingTime κ s)] at hc
  exact (condExp_congr_ae he).symm.trans hc

/-- The same actual law in the ambient-null-augmented observed filtration. -/
theorem conditional_augmented (κ s h : ℝ≥0) (f : ℝ → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : ∀ x, ‖f x‖ ≤ M) :
    gaussianProduct[(fun ω => f (BrownianMassRandomTimeChange.changedPath κ ω (s+h))) |
      StickyNaturalClock.augmentedNaturalPast κ s] =ᵐ[gaussianProduct]
    (fun ω => ∫ p, f (value κ h (BrownianMassRandomTimeChange.changedPath κ ω s) p)
      ∂gaussianProduct.map clockPath) := by
  have hi : Integrable (fun ω => f (BrownianMassRandomTimeChange.changedPath κ ω (s+h)))
      gaussianProduct := Integrable.of_bound
    (hf.comp (BrownianMassRandomTimeChange.changedPath_coordinate_measurable κ (s+h))).aestronglyMeasurable
    M (Eventually.of_forall (fun ω => hM _))
  exact (AmbientNullAugmentation.condExp_invariant (StickyNaturalClock.naturalPast κ s)
    gaussianProduct ((StickyNaturalClock.naturalPast κ).le s) _ hi).symm.trans
      (conditional_raw κ s h f hf M hM)

end OperatorDerivativeRewrite.Foundation.StickyStateSplice
