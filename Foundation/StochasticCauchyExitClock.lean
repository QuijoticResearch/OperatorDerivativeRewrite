import Foundation.StochasticCauchyStoppedIndicators
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.Monotone

/-! Actual continuous radial exit clocks and native bounded-horizon integration. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyExitClock
open InfiniteGaussian StochasticCauchyStoppedDomains StochasticCauchyStoppedIndicators
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyPhysicalInput StochasticCauchyExponentialInput StochasticCauchyComplexChannels
open StochasticCauchyBrownianRealization
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyComplexChannels.complexInput_complete
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct

/-- Clip BEFORE removing the top value: an infinite clock becomes T, never0. -/
def clippedClock (T : ℝ≥0) (τ : Sample → WithTop ℝ≥0) (w : Sample) : ℝ≥0 :=
  (min (τ w) (T:WithTop ℝ≥0)).untopD 0

theorem clippedClock_coe (T : ℝ≥0) (τ : Sample → WithTop ℝ≥0) (w : Sample) :
    (clippedClock T τ w:WithTop ℝ≥0)=min (τ w) (T:WithTop ℝ≥0) := by
  cases h : τ w with
  | top => rw [clippedClock,h,min_eq_right le_top,WithTop.untopD_coe]
  | coe t => rw [clippedClock,h,← WithTop.coe_min,WithTop.untopD_coe]

theorem clippedClock_le (T : ℝ≥0) (τ : Sample → WithTop ℝ≥0) (w : Sample) : clippedClock T τ w≤T := by
  exact_mod_cast (show (clippedClock T τ w:WithTop ℝ≥0)≤(T:WithTop ℝ≥0) by
    rw [clippedClock_coe];exact min_le_right _ _)

theorem clippedClock_stopping (T : ℝ≥0) (τ : Sample → WithTop ℝ≥0) (hτ : IsStoppingTime augmentedJoint τ) :
    IsStoppingTime augmentedJoint (fun w => (clippedClock T τ w:WithTop ℝ≥0)) := by
  simpa only [clippedClock_coe] using hτ.min_const T

def stoppedInput (T : ℝ≥0) (τ : Sample → WithTop ℝ≥0) (hτ : IsStoppingTime augmentedJoint τ) : Input T :=
  StochasticCauchyStoppedIndicators.stoppedInput (clippedClock T τ) (clippedClock_stopping T τ hτ) T

def stoppedComplexInput (T : ℝ≥0) (τ : Sample → WithTop ℝ≥0) (hτ : IsStoppingTime augmentedJoint τ) : ComplexInput T :=
  StochasticCauchyStoppedIndicators.stoppedComplexInput (clippedClock T τ) (clippedClock_stopping T τ hτ) T

theorem stopped_actual (T : ℝ≥0) (τ : Sample → WithTop ℝ≥0) (hτ : IsStoppingTime augmentedJoint τ) :
    channel T false (stoppedComplexInput T τ hτ) =ᵐ[μ] fun w => value (clippedClock T τ w) w := by
  filter_upwards [stopped_channel_actual (clippedClock T τ) (clippedClock_stopping T τ hτ) T] with w hw
  simpa only [stoppedComplexInput,StochasticCauchyStoppedDomains.stopped,min_eq_right (clippedClock_le T τ w)] using hw

theorem stopped_memLp (T : ℝ≥0) (τ : Sample → WithTop ℝ≥0) (hτ : IsStoppingTime augmentedJoint τ) :
    MemLp (fun w => value (clippedClock T τ w) w) 2 μ :=
  (Lp.memLp (channel T false (stoppedComplexInput T τ hτ))).ae_eq (stopped_actual T τ hτ)

theorem stopped_mean_zero (T : ℝ≥0) (τ : Sample → WithTop ℝ≥0) (hτ : IsStoppingTime augmentedJoint τ) :
    (∫ w,value (clippedClock T τ w) w ∂μ)=0 := by
  rw [← integral_congr_ae (stopped_actual T τ hτ)]
  exact StochasticCauchyMeanResidual.channel_centered T false _

private def hits (R : ℝ) (w : Sample) : Set ℝ≥0 := {t | R≤‖value t w‖}
private theorem hits_closed (R : ℝ) (w : Sample) : IsClosed (hits R w) :=
  isClosed_le continuous_const (value_continuous w).norm

/-- Actual first hit of the closed exterior of the radius-R disk.
An empty hit set gives the genuine infinite clock. -/
def exitTime (R : ℝ) (w : Sample) : WithTop ℝ≥0 := by
  classical
  exact if h : (hits R w).Nonempty then (sInf (hits R w):ℝ≥0) else ⊤

theorem exitTime_le_iff (R : ℝ) (T : ℝ≥0) (w : Sample) :
    exitTime R w≤T ↔ ∃ s : ℝ≥0,s≤T ∧ R≤‖value s w‖ := by
  classical
  by_cases h : (hits R w).Nonempty
  · rw [exitTime,dite_eq_left h,WithTop.coe_le_coe]
    constructor
    · intro hT
      exact ⟨sInf (hits R w),hT,(hits_closed R w).csInf_mem h (OrderBot.bddBelow _)⟩
    · rintro ⟨s,hs,hR⟩
      exact (csInf_le (s := hits R w) (OrderBot.bddBelow _) (show s∈hits R w from hR)).trans hs
  · rw [exitTime,dite_eq_right h]
    simp only [WithTop.top_le_iff,WithTop.coe_ne_top,false_iff,not_exists,not_and]
    intro s hs hR;exact h ⟨s,hR⟩

private instance horizon_nonempty (T : ℝ≥0) : Nonempty (Icc (0:ℝ≥0) T) := ⟨⟨0,⟨bot_le,bot_le⟩⟩⟩
private def observedPath (T : ℝ≥0) (w : Sample) : C(Icc (0:ℝ≥0) T,ℂ) :=
  ⟨fun s => value s.val w,(value_continuous w).comp continuous_subtype_val⟩

private theorem observedPath_measurable (T : ℝ≥0) : Measurable[augmentedJoint T] (observedPath T) := by
  let : MeasurableSpace Sample := augmentedJoint T
  apply ContinuousMap.measurable_iff_eval.mpr
  intro s
  exact ((continuous_stronglyAdapted s.val).mono (augmentedJoint.mono s.property.2)).measurable

private theorem hit_iff_norm (R : ℝ) (T : ℝ≥0) (w : Sample) :
    (∃ s : ℝ≥0,s≤T ∧ R≤‖value s w‖) ↔ R≤‖observedPath T w‖ := by
  constructor
  · rintro ⟨s,hs,hR⟩
    exact hR.trans ((observedPath T w).norm_coe_le_norm ⟨s,⟨bot_le,hs⟩⟩)
  · intro hR
    obtain ⟨s,hs,hmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (Set.univ : Set (Icc (0:ℝ≥0) T)).Nonempty)
      (observedPath T w).continuous.norm.continuousOn
    have hn : ‖observedPath T w‖≤‖observedPath T w s‖ :=
      ((observedPath T w).norm_le (norm_nonneg _)).mpr (fun x => hmax (Set.mem_univ x))
    exact ⟨s.val,s.property.2,hR.trans hn⟩

/-- Continuous closed-target first hitting is a stopping time in the ACTUAL
observed joint filtration. No discrete-time hitting theorem is invoked. -/
theorem exitTime_stopping (R : ℝ) : IsStoppingTime augmentedJoint (exitTime R) := by
  intro T
  have he : {w | exitTime R w≤T}={w | R≤‖observedPath T w‖} := by
    ext w;exact (exitTime_le_iff R T w).trans (hit_iff_norm R T w)
  rw [he]
  let : MeasurableSpace Sample := augmentedJoint T
  exact measurableSet_le measurable_const (observedPath_measurable T).norm

/-- Every time strictly before the first closed-exterior hit is genuinely inside. -/
theorem before_exit (R : ℝ) (w : Sample) (s : ℝ≥0) (hs : (s:WithTop ℝ≥0)<exitTime R w) :
    ‖value s w‖<R := by
  by_contra h
  have he : exitTime R w≤s := (exitTime_le_iff R s w).mpr ⟨s,le_rfl,le_of_not_gt h⟩
  exact (not_le_of_gt hs) he

/-- A finite first exit actually attains the closed exterior. -/
theorem exit_attains (R : ℝ) (w : Sample) (s : ℝ≥0) (hs : exitTime R w=s) : R≤‖value s w‖ := by
  obtain ⟨t,ht,hR⟩ := (exitTime_le_iff R s w).mp hs.le
  have hst : s≤t := by
    have he := (exitTime_le_iff R t w).mpr ⟨t,le_rfl,hR⟩
    rw [hs] at he;exact_mod_cast he
  have he : t=s := le_antisymm ht hst
  simpa only [he] using hR

/-- Continuous first exit lands on the boundary, provided the initial point
is in the closed disk. No exit finiteness is assumed; this is conditional on
an actual finite value of the constructed clock. -/
theorem exit_boundary (R : ℝ) (w : Sample) (s : ℝ≥0)
    (h0 : ‖value 0 w‖≤R) (hs : exitTime R w=s) : ‖value s w‖=R := by
  apply le_antisymm _ (exit_attains R w s hs)
  by_contra h
  have hRs : R<‖value s w‖ := lt_of_not_ge h
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (show (0:ℝ≥0)≤s from bot_le)
    (value_continuous w).norm.continuousOn ⟨h0,hRs.le⟩
  have hts : t<s := lt_of_le_of_ne ht.2 (by intro hts;rw [hts] at he;exact hRs.ne' he)
  have hb := before_exit R w t (by rw [hs];exact_mod_cast hts)
  exact hb.ne he

/-- The actual clipped exit value stays in the closed disk, even on paths
whose first-exit clock is infinite. -/
theorem exit_stopped_bound (R : ℝ) (T : ℝ≥0) (w : Sample) (h0 : ‖value 0 w‖≤R) :
    ‖value (clippedClock T (exitTime R) w) w‖≤R := by
  by_cases he : exitTime R w≤T
  · have hc : exitTime R w=(clippedClock T (exitTime R) w:WithTop ℝ≥0) := by
      rw [clippedClock_coe,min_eq_left he]
    exact (exit_boundary R w _ h0 hc).le
  · have hc : clippedClock T (exitTime R) w=T := by
      apply WithTop.coe_injective
      rw [clippedClock_coe,min_eq_right (le_of_not_ge he)]
    rw [hc]
    exact (before_exit R w T (lt_of_not_ge he)).le

def exitInput (R : ℝ) (T : ℝ≥0) : Input T := stoppedInput T (exitTime R) (exitTime_stopping R)
def exitComplexInput (R : ℝ) (T : ℝ≥0) : ComplexInput T := stoppedComplexInput T (exitTime R) (exitTime_stopping R)

theorem exit_stochastic_actual (R : ℝ) (T : ℝ≥0) :
    channel T false (exitComplexInput R T) =ᵐ[μ] fun w => value (clippedClock T (exitTime R) w) w :=
  stopped_actual T (exitTime R) (exitTime_stopping R)

theorem exit_memLp (R : ℝ) (T : ℝ≥0) :
    MemLp (fun w => value (clippedClock T (exitTime R) w) w) 2 μ :=
  stopped_memLp T (exitTime R) (exitTime_stopping R)

theorem exit_mean_zero (R : ℝ) (T : ℝ≥0) :
    (∫ w,value (clippedClock T (exitTime R) w) w ∂μ)=0 :=
  stopped_mean_zero T (exitTime R) (exitTime_stopping R)

theorem exit_bounded_ae (R : ℝ) (hR : 0≤R) (T : ℝ≥0) :
    ∀ᵐ w ∂μ,‖value (clippedClock T (exitTime R) w) w‖≤R := by
  filter_upwards [value_zero_ae] with w hw
  exact exit_stopped_bound R T w (by simpa only [hw,norm_zero] using hR)

/-- The physical native indicator includes infinite clocks correctly. -/
theorem stopped_physical (T : ℝ≥0) (τ : Sample → WithTop ℝ≥0) (hτ : IsStoppingTime augmentedJoint τ) :
    ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,fieldEmbedding T (stoppedInput T τ hτ) ((r,w.1),w.2)=
      {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤τ w}.indicator (fun _ => (1:ℝ)) w := by
  filter_upwards [StochasticCauchyStoppedIndicators.stoppedInput_physical (clippedClock T τ)
    (clippedClock_stopping T τ hτ) T,ae_restrict_mem (μ := volume) measurableSet_Ioc] with r hr hin
  filter_upwards [hr] with w hw
  change fieldEmbedding T (StochasticCauchyStoppedIndicators.stoppedInput (clippedClock T τ)
    (clippedClock_stopping T τ hτ) T) ((r,w.1),w.2)=_
  rw [hw]
  have hrT : r.toNNReal≤T := Real.toNNReal_le_iff_le_coe.mpr hin.2
  have he : r≤(clippedClock T τ w:ℝ) ↔ (r.toNNReal:WithTop ℝ≥0)≤τ w := by
    rw [← Real.toNNReal_le_iff_le_coe,← WithTop.coe_le_coe,clippedClock_coe,le_min_iff]
    simp only [WithTop.coe_le_coe,hrT,and_true]
  simp only [Set.indicator,Set.mem_Ioc,Set.mem_ofPred_eq,hin.1,true_and,he]

theorem exitInput_physical (R : ℝ) (T : ℝ≥0) :
    ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,fieldEmbedding T (exitInput R T) ((r,w.1),w.2)=
      {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤exitTime R w}.indicator (fun _ => (1:ℝ)) w :=
  stopped_physical T (exitTime R) (exitTime_stopping R)

theorem exit_top_iff (R : ℝ) (w : Sample) : exitTime R w=⊤ ↔ ∀ t : ℝ≥0,‖value t w‖<R := by
  constructor
  · intro h t;exact before_exit R w t (by rw [h];exact WithTop.coe_lt_top _)
  · intro h
    cases he : exitTime R w with
    | top => rfl
    | coe t => exact False.elim ((not_le_of_gt (h t)) (exit_attains R w t he))

/-- The genuine native stopped input has a UNIFORM horizon energy bound.
No finite mean exit-time conclusion is inferred without the occupation identity. -/
theorem exit_input_energy (R : ℝ) (hR : 0≤R) (T : ℝ≥0) : ‖exitInput R T‖^2≤R^2/2 := by
  have ha := StochasticCauchyStoppedIndicators.stoppedValue_actual
    (clippedClock T (exitTime R)) (clippedClock_stopping T (exitTime R) (exitTime_stopping R)) T
  have hb : ∀ᵐ w ∂μ,‖StochasticCauchyStoppedIndicators.valueIntegral T (exitInput R T) w‖≤R := by
    filter_upwards [ha,exit_bounded_ae R hR T] with w hw hb
    change StochasticCauchyStoppedIndicators.valueIntegral T (exitInput R T) w=_ at hw
    rw [hw]
    simpa only [StochasticCauchyStoppedDomains.stopped,min_eq_right (clippedClock_le T (exitTime R) w)] using hb
  have hn : ‖StochasticCauchyStoppedIndicators.valueIntegral T (exitInput R T)‖≤R := by
    simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (μ := μ) hR hb
  have he : ‖StochasticCauchyStoppedIndicators.valueIntegral T (exitInput R T)‖^2=2*‖exitInput R T‖^2 := by
    change ‖ComplexL2Isometry.combine μ (integralX T (exitInput R T)) (integralY T (exitInput R T))‖^2=_
    rw [ComplexL2Isometry.combine_norm_sq,(integralX T).norm_map,(integralY T).norm_map]
    ring
  nlinarith [norm_nonneg (StochasticCauchyStoppedIndicators.valueIntegral T (exitInput R T))]

/-- Actual finite chronological sums converge in physical mean square even
when the original exit clock might be infinite. -/
theorem exit_mean_square (R : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => ∫ w,‖chronologicalSum (clippedClock T (exitTime R)) T n w-
      value (clippedClock T (exitTime R) w) w‖^2 ∂μ) atTop (𝓝 0) := by
  have h := chronological_mean_square (clippedClock T (exitTime R))
    (clippedClock_stopping T (exitTime R) (exitTime_stopping R)) T
  have he : StochasticCauchyStoppedDomains.stopped T (clippedClock T (exitTime R))=
      fun w => value (clippedClock T (exitTime R) w) w := by
    funext w
    exact congrArg (fun t => value t w) (min_eq_right (clippedClock_le T (exitTime R) w))
  simpa only [he] using h

end OperatorDerivativeRewrite.Foundation.StochasticCauchyExitClock
