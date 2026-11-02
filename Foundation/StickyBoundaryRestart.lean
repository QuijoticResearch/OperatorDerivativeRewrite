import Foundation.StickyRestartRealization
import Foundation.BrownianStickyBoundaryAtom
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Boundary restart of the actual sticky clock, from the original smooth mass
approximation and Brownian path restart law. No all-start semigroup is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyBoundaryRestart
open InfiniteGaussian IBMConstructedSources BrownianMassClockStoppingTime
open BrownianMassPathFunctional BrownianMassContinuousLimit BrownianMassFastSubsequence
open SmoothAbsoluteApproximation RealSteklovApprox

/-- The existing smooth mass approximant evaluated on an arbitrary continuous path. -/
def primitive (n : ℕ) (p : C(ℝ≥0, ℝ)) (t : ℝ) : ℝ :=
  (1/2 : ℝ) * ∫ s in 0..t, curvature (width n) (p s.toNNReal)

theorem primitive_hasDerivAt (n : ℕ) (p : C(ℝ≥0, ℝ)) (t : ℝ) :
    HasDerivAt (primitive n p) ((1/2 : ℝ)*curvature (width n) (p t.toNNReal)) t := by
  have hc := (BrownianSmoothMassPath.curvature_continuous (width_pos n)).comp
    (p.continuous.comp continuous_real_toNNReal)
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul (1/2 : ℝ)

def approximation (n : ℕ) (p : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun t => primitive n p t,
    (continuous_iff_continuousAt.mpr (fun t => (primitive_hasDerivAt n p t).continuousAt)).comp
      NNReal.continuous_coe⟩

theorem approximation_brownian (n : ℕ) (ω : SampleSpace) :
    approximation n (clockPath ω) = BrownianSmoothMassPath.path n ω := rfl

theorem approximation_measurable (n : ℕ) : Measurable (approximation n) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro T
  change Measurable (fun p : C(ℝ≥0, ℝ) => primitive n p (T : ℝ))
  have hev : Measurable (fun z : C(ℝ≥0, ℝ) × ℝ≥0 => z.1 z.2) :=
    continuous_eval.measurable
  have harg : Measurable (fun z : C(ℝ≥0, ℝ) × ℝ => (z.1, z.2.toNNReal)) :=
    measurable_fst.prodMk measurable_snd.real_toNNReal
  have hr : Measurable (fun z : C(ℝ≥0, ℝ) × ℝ => curvature (width n) (z.1 z.2.toNNReal)) :=
    (BrownianSmoothMassPath.curvature_continuous (width_pos n)).measurable.comp (hev.comp harg)
  have hi : StronglyMeasurable (fun p : C(ℝ≥0, ℝ) =>
      ∫ s, curvature (width n) (p s.toNNReal) ∂volume.restrict (Ioc 0 (T : ℝ))) :=
    hr.stronglyMeasurable.integral_prod_right'
  simp only [primitive, intervalIntegral.integral_of_le T.coe_nonneg]
  exact hi.measurable.const_mul (1/2 : ℝ)

/-- One Borel full-path event, not a per-time exceptional-set assertion. -/
def Good (p : C(ℝ≥0, ℝ)) : Prop :=
  Tendsto (fun j => approximation (subsequence j) p) atTop (nhds (functional p)) ∧
    functional p 0 = 0 ∧ Monotone (functional p)

theorem good_measurable : MeasurableSet {p | Good p} := by
  exact (measurableSet_tendsto_fun (fun j => approximation_measurable (subsequence j))
    functional_measurable).inter
      (((isClosed_eq (continuous_eval_const 0) continuous_const).measurableSet.preimage
        functional_measurable).inter
        (StickyWienerPathRealization.monotone_set_measurable.preimage functional_measurable))

theorem original_good : ∀ᵐ ω ∂gaussianProduct, Good (clockPath ω) := by
  filter_upwards [functional_agrees, limitPath_tendsto, limitPath_properties] with ω hf ht hp
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [approximation_brownian]
    rwa [hf]
  · rw [hf]; exact hp.1
  · rw [hf]; exact hp.2.1

theorem wiener_good : ∀ᵐ p ∂gaussianProduct.map clockPath, Good p :=
  (ae_map_iff clockPath_measurable.aemeasurable good_measurable).mpr original_good

def shift (p : C(ℝ≥0, ℝ)) (a : ℝ≥0) : C(ℝ≥0, ℝ) :=
  ⟨fun t => p (a+t)-p a, (p.continuous.comp (continuous_const.add continuous_id)).sub
    continuous_const⟩

/-- Exact additive identity BEFORE taking any stochastic limit. -/
theorem approximation_shift (n : ℕ) (p : C(ℝ≥0, ℝ)) (a u : ℝ≥0) (hz : p a = 0) :
    approximation n (shift p a) u = approximation n p (a+u) - approximation n p a := by
  have hc := (BrownianSmoothMassPath.curvature_continuous (width_pos n)).comp
    (p.continuous.comp continuous_real_toNNReal)
  have he : (∫ s in (0:ℝ)..(u:ℝ), curvature (width n) (shift p a s.toNNReal)) =
      ∫ s in (0:ℝ)..(u:ℝ), curvature (width n) (p ((a:ℝ)+s).toNNReal) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le u.coe_nonneg] at hs
    have ha : a+s.toNNReal = ((a:ℝ)+s).toNNReal := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_add, Real.coe_toNNReal _ hs.1,
        Real.coe_toNNReal _ (add_nonneg a.coe_nonneg hs.1)]
    simp only [shift, ContinuousMap.coe_mk, hz, sub_zero, ha]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := (volume : Measure ℝ))
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a ((a:ℝ)+u))
  change (1/2 : ℝ) * _ = (1/2 : ℝ)*_ - (1/2 : ℝ)*_
  have hshift := intervalIntegral.integral_comp_add_left
    (fun s : ℝ => curvature (width n) (p s.toNNReal)) (a : ℝ) (a := 0) (b := (u : ℝ))
  rw [he, hshift]
  simp only [add_zero, NNReal.coe_add, Function.comp_def] at *
  linarith

/-- The original chosen limit functional is additive at a zero restart,
provided BOTH original and shifted paths lie in its verified Borel good event. -/
theorem functional_shift (p : C(ℝ≥0, ℝ)) (a u : ℝ≥0)
    (hp : Good p) (hs : Good (shift p a)) (hz : p a = 0) :
    functional (shift p a) u = functional p (a+u) - functional p a := by
  have ht := (continuous_eval_const u).continuousAt.tendsto.comp hs.1
  have h1 := (continuous_eval_const (a+u)).continuousAt.tendsto.comp hp.1
  have h0 := (continuous_eval_const a).continuousAt.tendsto.comp hp.1
  apply tendsto_nhds_unique ht
  convert h1.sub h0 using 1
  funext j
  exact approximation_shift (subsequence j) p a u hz

theorem good_mass_coe (p : C(ℝ≥0, ℝ)) (hp : Good p) (t : ℝ≥0) :
    (StickyWienerPathRealization.mass p t : ℝ) = functional p t := by
  simp only [StickyWienerPathRealization.mass, StickyWienerPathRealization.cumulativePath,
    if_pos hp.2.2, hp.2.1, sub_zero]
  exact Real.coe_toNNReal _ (by rw [← hp.2.1]; exact hp.2.2 (show (0 : ℝ≥0) ≤ t from bot_le))

theorem mass_shift (p : C(ℝ≥0, ℝ)) (a u : ℝ≥0)
    (hp : Good p) (hs : Good (shift p a)) (hz : p a = 0) :
    StickyWienerPathRealization.mass p (a+u) = StickyWienerPathRealization.mass p a +
      StickyWienerPathRealization.mass (shift p a) u := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_add, good_mass_coe p hp, good_mass_coe (shift p a) hs]
  have h := functional_shift p a u hp hs hz
  linarith

/-- Passing through the ORIGINAL invertible clock yields the physical-time
inverse restart identity; it is not an operational-time increment identity. -/
theorem inverse_shift (κ : ℝ≥0) (p : C(ℝ≥0, ℝ)) (a u : ℝ≥0)
    (hp : Good p) (hs : Good (shift p a)) (hz : p a = 0) :
    StickyWienerPathRealization.inverse κ p
        (StickyTimeChangeClock.clock κ (StickyWienerPathRealization.mass p) a + u) =
      a + StickyWienerPathRealization.inverse κ (shift p a) u := by
  have hu : StickyWienerPathRealization.inverse κ (shift p a) u +
      κ * StickyWienerPathRealization.mass (shift p a)
        (StickyWienerPathRealization.inverse κ (shift p a) u) = u :=
    StickyTimeChangeClock.clock_inverse κ _ _ _ _ u
  have ha : StickyTimeChangeClock.clock κ (StickyWienerPathRealization.mass p)
      (a + StickyWienerPathRealization.inverse κ (shift p a) u) =
      StickyTimeChangeClock.clock κ (StickyWienerPathRealization.mass p) a + u := by
    dsimp only [StickyTimeChangeClock.clock]
    rw [mass_shift p a _ hp hs hz, mul_add]
    calc
      _ = a + κ * StickyWienerPathRealization.mass p a +
          (StickyWienerPathRealization.inverse κ (shift p a) u +
            κ * StickyWienerPathRealization.mass (shift p a)
              (StickyWienerPathRealization.inverse κ (shift p a) u)) := by ring
      _ = _ := by rw [hu]
  apply (StickyTimeChangeClock.clock_strictMono κ _
    (StickyWienerPathRealization.mass_monotone p)).injective
  rw [StickyWienerPathRealization.inverse, StickyTimeChangeClock.clock_inverse]
  exact ha.symm

theorem sticky_shift (κ : ℝ≥0) (p : C(ℝ≥0, ℝ)) (a u : ℝ≥0)
    (hp : Good p) (hs : Good (shift p a)) (hz : p a = 0) :
    StickyWienerPathRealization.stickyPath κ p
        (StickyTimeChangeClock.clock κ (StickyWienerPathRealization.mass p) a + u) =
      StickyWienerPathRealization.stickyPath κ (shift p a) u := by
  change p (StickyWienerPathRealization.inverse κ p _) =
    shift p a (StickyWienerPathRealization.inverse κ (shift p a) u)
  rw [inverse_shift κ p a u hp hs hz]
  simp only [shift, ContinuousMap.coe_mk, hz, sub_zero]

variable (τ : SampleSpace → ℝ≥0)
  (hτ : IsStoppingTime augmentedPast (fun ω => (τ ω : WithTop ℝ≥0)))

include hτ in
theorem restarted_good : ∀ᵐ ω ∂gaussianProduct,
    Good (BrownianBoundedRestartProcess.path τ ω) := by
  have h : ∀ᵐ p ∂gaussianProduct.map (BrownianBoundedRestartProcess.path τ), Good p := by
    rw [BrownianFiniteStrongMarkov.path_law τ hτ]
    exact wiener_good
  exact ae_of_ae_map (BrownianBoundedRestartProcess.path_measurable τ hτ).aemeasurable h

/-- Actual physical continuation agrees with the independently realized fresh
sticky path ON the boundary event. One exceptional set handles every future time. -/
theorem physical_boundary_restart (κ s : ℝ≥0) : ∀ᵐ ω ∂gaussianProduct,
    BrownianMassRandomTimeChange.changedPath κ ω s = 0 → ∀ u : ℝ≥0,
      BrownianMassRandomTimeChange.changedPath κ ω (s+u) =
        StickyRestartRealization.restartedSticky κ
          (fun w => BrownianMassRandomTimeChange.inverse κ w s) ω u := by
  let τ : SampleSpace → ℝ≥0 := fun w => BrownianMassRandomTimeChange.inverse κ w s
  have hτ := inverse_isStoppingTime κ s
  filter_upwards [original_good, restarted_good τ hτ,
    StickyWienerPathRealization.mass_agrees, StickyWienerPathRealization.stickyPath_agrees]
    with ω hp hr hm hpath hz u
  have hs : Good (shift (clockPath ω) (τ ω)) := hr
  have hb : clockPath ω (τ ω) = 0 := hz
  have hf : StickyTimeChangeClock.clock κ (StickyWienerPathRealization.mass (clockPath ω))
      (τ ω) = s := by
    rw [hm]
    exact BrownianMassRandomTimeChange.forward_inverse κ ω s
  have he := sticky_shift κ (clockPath ω) (τ ω) u hp hs hb
  rw [hf, hpath κ] at he
  exact he

/-- Boundary-conditioned nonlinear future laws are the original fresh sticky
laws. This is an actual physical-time probability identity, not a surrogate. -/
theorem boundary_past_factorization (κ s u : ℝ≥0) (H : Set SampleSpace)
    (hH : MeasurableSet[StickyNaturalClock.augmentedNaturalPast κ s] H)
    (hzero : ∀ ω ∈ H, BrownianMassRandomTimeChange.changedPath κ ω s = 0)
    (A : Set ℝ) (hA : MeasurableSet A) :
    gaussianProduct {ω | ω ∈ H ∧
      BrownianMassRandomTimeChange.changedPath κ ω (s+u) ∈ A} =
    gaussianProduct H *
      gaussianProduct {ω | BrownianMassRandomTimeChange.changedPath κ ω u ∈ A} := by
  let τ : SampleSpace → ℝ≥0 := fun w => BrownianMassRandomTimeChange.inverse κ w s
  let R := StickyRestartRealization.restartedSticky κ τ
  let E : Set SampleSpace := H
  let F : Set SampleSpace := {ω | R ω u ∈ A}
  have hτ := inverse_isStoppingTime κ s
  have hE : MeasurableSet[StickyNaturalClock.augmentedNaturalPast κ s] E := hH
  have hev : MeasurableSet {p : C(ℝ≥0, ℝ) | p u ∈ A} :=
    hA.preimage (ContinuousMap.measurable_eval u)
  have hF : MeasurableSet[MeasurableSpace.comap R inferInstance] F := ⟨_, hev, rfl⟩
  have hi := StickyRestartRealization.inverse_clock_independent_observed κ κ s
  have hprod := (hi.symm.indepSet_of_measurableSet hE hF).measure_inter_eq_mul
  have he : {ω | ω ∈ H ∧
      BrownianMassRandomTimeChange.changedPath κ ω (s+u) ∈ A} =ᵐ[gaussianProduct] E ∩ F := by
    filter_upwards [physical_boundary_restart κ s] with ω hω
    by_cases hmem : ω ∈ H
    · have hz := hzero ω hmem
      simp only [E, F, Set.mem_setOf_eq, Set.mem_inter_iff, hmem, true_and]
      rw [hω hz u]
    · simp [E, F, hmem]
  have hl := congrArg (fun ν : Measure C(ℝ≥0, ℝ) => ν {p | p u ∈ A})
    (StickyRestartRealization.path_law κ τ hτ)
  rw [Measure.map_apply (StickyRestartRealization.path_measurable κ τ hτ) hev,
    Measure.map_apply (BrownianMassRandomTimeChange.changedPath_measurable κ) hev] at hl
  calc
    _ = gaussianProduct (E ∩ F) := measure_congr he
    _ = gaussianProduct E * gaussianProduct F := hprod
    _ = _ := by rw [show gaussianProduct F =
        gaussianProduct {ω | BrownianMassRandomTimeChange.changedPath κ ω u ∈ A} from hl]

/-- Specialization to the entire observed boundary event. -/
theorem boundary_future_factorization (κ s u : ℝ≥0) (A : Set ℝ) (hA : MeasurableSet A) :
    gaussianProduct {ω | BrownianMassRandomTimeChange.changedPath κ ω s = 0 ∧
      BrownianMassRandomTimeChange.changedPath κ ω (s+u) ∈ A} =
    gaussianProduct {ω | BrownianMassRandomTimeChange.changedPath κ ω s = 0} *
      gaussianProduct {ω | BrownianMassRandomTimeChange.changedPath κ ω u ∈ A} := by
  apply boundary_past_factorization κ s u _
    (measurableSet_eq_fun (StickyNaturalMartingales.state_augmented_adapted κ s).measurable
      measurable_const) (fun _ h => h) A hA

/-- At a positive-mass boundary atom, the pre-existing regular conditional
kernel has the actual fresh sticky marginal as its row, for every Borel set. -/
theorem boundary_kernel_row (κ s u : ℝ≥0)
    (hs : BrownianTimeChangedConditionalKernel.marginal κ s {0} ≠ 0) :
    BrownianTimeChangedConditionalKernel.pairKernel κ s (s+u) 0 =
      BrownianTimeChangedConditionalKernel.marginal κ u := by
  apply Measure.ext
  intro A hA
  rw [BrownianStickyBoundaryAtom.boundary_row_formula κ s (s+u) hs A]
  have hp : BrownianTimeChangedConditionalKernel.pairLaw κ s (s+u) ({0} ×ˢ A) =
      BrownianTimeChangedConditionalKernel.marginal κ s {0} *
        BrownianTimeChangedConditionalKernel.marginal κ u A := by
    rw [BrownianTimeChangedConditionalKernel.pairLaw,
      Measure.map_apply ((BrownianTimeChangedConditionalKernel.state_measurable κ s).prodMk
        (BrownianTimeChangedConditionalKernel.state_measurable κ (s+u)))
        ((measurableSet_singleton (0 : ℝ)).prod hA)]
    simp only [BrownianTimeChangedConditionalKernel.marginal,
      Measure.map_apply (BrownianTimeChangedConditionalKernel.state_measurable κ s)
        (measurableSet_singleton (0 : ℝ)),
      Measure.map_apply (BrownianTimeChangedConditionalKernel.state_measurable κ u) hA]
    simpa only [BrownianTimeChangedConditionalKernel.state, Set.preimage,
      Set.mem_prod, Set.mem_singleton_iff] using boundary_future_factorization κ s u A hA
  rw [hp, ← mul_assoc, ENNReal.inv_mul_cancel hs (measure_ne_top _ _), one_mul]

/-- For positive stickiness the boundary restart is nonvacuous at some
strictly positive deterministic time in every positive horizon. -/
theorem exists_nontrivial_boundary_restart (κ T : ℝ≥0) (hκ : 0 < κ) (hT : 0 < T) :
    ∃ s : ℝ≥0, 0 < s ∧ s ≤ T ∧
      0 < gaussianProduct {ω | BrownianMassRandomTimeChange.changedPath κ ω s = 0} ∧
      (∀ᵐ ω ∂gaussianProduct, BrownianMassRandomTimeChange.changedPath κ ω s = 0 →
        ∀ u : ℝ≥0, BrownianMassRandomTimeChange.changedPath κ ω (s+u) =
          StickyRestartRealization.restartedSticky κ
            (fun w => BrownianMassRandomTimeChange.inverse κ w s) ω u) := by
  obtain ⟨s, hs, hsT, hp⟩ := BrownianStickyBoundaryAtom.exists_boundary_atom κ T hκ hT
  exact ⟨s, hs, hsT, hp, physical_boundary_restart κ s⟩

end OperatorDerivativeRewrite.Foundation.StickyBoundaryRestart
