import Foundation.StochasticCauchyAnalyticDisk
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyAnalyticMartingale
open InfiniteGaussian StochasticCauchyExitClock StochasticCauchyStoppedDomains
open StochasticCauchyExitMoments StochasticCauchyBrownianRealization
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct

private theorem clipped_adapted (M : ℝ≥0 → Sample → ℂ)
    (ha : StronglyAdapted augmentedJoint M) (hc : ∀ w,Continuous (fun t => M t w))
    (τ : Sample → WithTop ℝ≥0) (hτ : IsStoppingTime augmentedJoint τ) :
    StronglyAdapted augmentedJoint (fun t w => M (clippedClock t τ w) w) := by
  intro t
  have h := (ha.stoppedProcess hc hτ) t
  convert h using 1
  funext w
  cases hw : τ w with
  | top =>
    change M (WithTop.untopD 0 (min (τ w) t)) w=M (min (t:WithTop ℝ≥0) (τ w)).untopA w
    rw [hw,min_eq_right le_top,min_eq_left le_top]
    rfl
  | coe u =>
    change M (WithTop.untopD 0 (min (τ w) t)) w=M (min (t:WithTop ℝ≥0) (τ w)).untopA w
    rw [hw,← WithTop.coe_min,← WithTop.coe_min,min_comm]
    rfl

/-- Bounded stopping preserves the ORIGINAL deterministic-past conditional
identity. Conditioning only at the stopped sigma-space would be weaker. -/
theorem clipped_condExp (M : ℝ≥0 → Sample → ℂ) (hm : Martingale M augmentedJoint μ)
    (hc : ∀ w,Continuous (fun t => M t w)) (τ : Sample → WithTop ℝ≥0)
    (hτ : IsStoppingTime augmentedJoint τ) (s t : ℝ≥0) (hst : s≤t) :
    μ[fun w => M (clippedClock t τ w) w | augmentedJoint s] =ᵐ[μ]
      fun w => M (clippedClock s τ w) w := by
  let η : Sample → ℝ≥0 := fun w => max s (clippedClock t τ w)
  have hη : IsStoppingTime augmentedJoint (fun w => (η w:WithTop ℝ≥0)) := by
    simpa only [η,WithTop.coe_max] using (isStoppingTime_const augmentedJoint s).max (clippedClock_stopping t τ hτ)
  have hηbound (w : Sample) : η w≤(⌈t⌉₊:ℝ≥0) :=
    (max_le hst (clippedClock_le t τ w)).trans (Nat.le_ceil t)
  have hintη := RightContinuousBoundedSampling.stopped_integrable μ augmentedJoint M hm
    (fun w => (hc w).isRightContinuous) η hη ⌈t⌉₊ hηbound
  have hint (u : ℝ≥0) : Integrable (fun w => M (clippedClock u τ w) w) μ :=
    RightContinuousBoundedSampling.stopped_integrable μ augmentedJoint M hm
      (fun w => (hc w).isRightContinuous) (clippedClock u τ) (clippedClock_stopping u τ hτ)
      ⌈u⌉₊ (fun w => (clippedClock_le u τ w).trans (Nat.le_ceil u))
  have hsample := RightContinuousBoundedSampling.sample_two μ augmentedJoint M hm
    (fun w => (hc w).isRightContinuous) η hη ⌈t⌉₊ hηbound
    (fun _ => s) (isStoppingTime_const augmentedJoint s) (fun w => le_max_left _ _)
  rw [IsStoppingTime.measurableSpace_const] at hsample
  have hsub : μ[fun w => M (η w) w-M s w | augmentedJoint s] =ᵐ[μ] fun _ => (0:ℂ) := by
    have hs := condExp_sub hintη (hm.integrable s) (augmentedJoint s)
    change μ[fun w => M (η w) w-M s w | augmentedJoint s] =ᵐ[μ] fun w => μ[fun w => M (η w) w | augmentedJoint s] w-μ[M s | augmentedJoint s] w at hs
    have hfix := condExp_of_stronglyMeasurable (augmented_joint_le s) (hm.stronglyAdapted s) (hm.integrable s)
    filter_upwards [hs,hsample] with w hw hv
    rw [hw,hfix,hv,sub_self]
  let A : Set Sample := {w | (s:WithTop ℝ≥0)<τ w}
  have hA : MeasurableSet[augmentedJoint s] A := by
    simpa only [A,← not_le,Set.compl_setOf] using (hτ s).compl
  have heq (w : Sample) : M (clippedClock t τ w) w-M (clippedClock s τ w) w=
      A.indicator (fun w => M (η w) w-M s w) w := by
    by_cases hw : w∈A
    · have hsτ : (s:WithTop ℝ≥0)<τ w := hw
      have hsclock : clippedClock s τ w=s := by
        apply WithTop.coe_injective
        rw [clippedClock_coe,min_eq_right hsτ.le]
      have htclock : s≤clippedClock t τ w := by
        apply WithTop.coe_le_coe.mp
        rw [clippedClock_coe]
        exact le_min hsτ.le (WithTop.coe_le_coe.mpr hst)
      rw [Set.indicator_of_mem hw,hsclock]
      simp only [η,max_eq_right htclock]
    · have hsτ : τ w≤(s:WithTop ℝ≥0) := le_of_not_gt hw
      have he : clippedClock t τ w=clippedClock s τ w := by
        apply WithTop.coe_injective
        rw [clippedClock_coe,clippedClock_coe,min_eq_left (hsτ.trans (WithTop.coe_le_coe.mpr hst)),min_eq_left hsτ]
      rw [Set.indicator_of_notMem hw,he,sub_self]
  have hzero : μ[fun w => M (clippedClock t τ w) w-M (clippedClock s τ w) w | augmentedJoint s]
      =ᵐ[μ] fun _ => (0:ℂ) := by
    have hh := condExp_indicator (hintη.sub (hm.integrable s)) hA
    change μ[A.indicator (fun w => M (η w) w-M s w) | augmentedJoint s] =ᵐ[μ]
      A.indicator (μ[fun w => M (η w) w-M s w | augmentedJoint s]) at hh
    filter_upwards [condExp_congr_ae (Eventually.of_forall heq),hh,hsub] with w he hi hs
    rw [he,hi]
    by_cases hw : w∈A <;> simp [hw,hs]
  have hfix := condExp_of_stronglyMeasurable (augmented_joint_le s) (clipped_adapted M hm.stronglyAdapted hc τ hτ s) (hint s)
  have hd := condExp_sub (hint t) (hint s) (augmentedJoint s)
  change μ[fun w => M (clippedClock t τ w) w-M (clippedClock s τ w) w | augmentedJoint s] =ᵐ[μ]
    fun w => μ[fun w => M (clippedClock t τ w) w | augmentedJoint s] w-μ[fun w => M (clippedClock s τ w) w | augmentedJoint s] w at hd
  filter_upwards [hzero,hd] with w hz hd
  rw [hd,hfix] at hz
  exact sub_eq_zero.mp hz
/-- A complex continuous extension supplies a genuinely measurable version;
f itself need not have any global regularity outside the specified disk. -/
theorem continuous_extension (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) :
    ∃ g : C(ℂ,ℂ),∀ z : ℂ,‖z‖≤R → g z=f z := by
  have hc : ContinuousOn f (Metric.closedBall 0 (R:ℝ)) :=
    hf.continuousOn.mono (Metric.closedBall_subset_ball (by exact_mod_cast hRS))
  let F : C(Metric.closedBall (0:ℂ) (R:ℝ),ℂ) := ⟨fun z => f z,hc.restrict⟩
  obtain ⟨g,hg⟩ := F.exists_restrict_eq Metric.isClosed_closedBall
  refine ⟨g,?_⟩
  intro z hz
  exact congrArg (fun H : C(Metric.closedBall (0:ℂ) (R:ℝ),ℂ) =>
    H ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using hz⟩) hg

private theorem clock_continuous (τ : Sample → WithTop ℝ≥0) (w : Sample) :
    Continuous (fun t => clippedClock t τ w) := by
  cases hw : τ w with
  | top =>
    simp only [clippedClock,hw,min_eq_right le_top,WithTop.untopD_coe]
    fun_prop
  | coe u =>
    simpa only [clippedClock,hw,← WithTop.coe_min,WithTop.untopD_coe] using
      (continuous_const.min continuous_id : Continuous (fun t : ℝ≥0 => min u t))

/-- ACTUAL continuous, strongly adapted martingale version of local holomorphic
stopped observables in the ORIGINAL augmented deterministic-past filtration.
No global f measurability or full Gaussian random-time derivative is assumed. -/
theorem exists_stopped_martingale (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) :
    ∃ G : ℝ≥0 → Sample → ℂ,Martingale G augmentedJoint μ ∧
      (∀ w,Continuous (fun t => G t w)) ∧
      (∀ t,G t =ᵐ[μ] fun w => f (value (clippedClock t (exitTime R) w) w)) ∧
      ∃ M : ℝ,0≤M ∧ ∀ t,∀ᵐ w ∂μ,‖G t w‖≤M := by
  obtain ⟨p,M,hM,hb,hl,hd⟩ := StochasticCauchyAnalyticDisk.analytic_approximation f R S hRS hf
  obtain ⟨g,hg⟩ := continuous_extension f R S hRS hf
  let G : ℝ≥0 → Sample → ℂ := fun t w => g (value (clippedClock t (exitTime R) w) w)
  have had : StronglyAdapted augmentedJoint G := by
    intro t
    exact g.continuous.comp_stronglyMeasurable
      (clipped_adapted value continuous_stronglyAdapted value_continuous (exitTime R) (exitTime_stopping R) t)
  have hactual (t : ℝ≥0) : G t =ᵐ[μ] fun w => f (value (clippedClock t (exitTime R) w) w) := by
    filter_upwards [exit_bounded_ae R R.coe_nonneg t] with w hw
    exact hg _ hw
  have hbound (t : ℝ≥0) : ∀ᵐ w ∂μ,‖G t w‖≤M := by
    filter_upwards [hactual t,exit_bounded_ae R R.coe_nonneg t] with w he hw
    rw [he]
    exact le_of_tendsto (hl _ hw).norm (Eventually.of_forall fun n => hb n _ hw)
  have hint (t : ℝ≥0) : Integrable (G t) μ :=
    (MemLp.of_bound ((had t).mono (augmented_joint_le t)).aestronglyMeasurable M (hbound t) : MemLp (G t) 2 μ).integrable (by norm_num)
  have hpolyint (n : ℕ) (t : ℝ≥0) : Integrable (fun w => polynomialProcess (p n) (clippedClock t (exitTime R) w) w) μ :=
    RightContinuousBoundedSampling.stopped_integrable μ augmentedJoint (polynomialProcess (p n))
      (polynomialProcess_martingale (p n)) (fun w => (polynomialProcess_continuous (p n) w).isRightContinuous)
      (clippedClock t (exitTime R)) (clippedClock_stopping t (exitTime R) (exitTime_stopping R))
      ⌈t⌉₊ (fun w => (clippedClock_le t (exitTime R) w).trans (Nat.le_ceil t))
  have hlim (t : ℝ≥0) : ∀ᵐ w ∂μ,Tendsto (fun n => polynomialProcess (p n) (clippedClock t (exitTime R) w) w) atTop (𝓝 (G t w)) := by
    filter_upwards [hactual t,exit_bounded_ae R R.coe_nonneg t] with w he hw
    rw [he]
    exact hl _ hw
  have hpb (n : ℕ) (t : ℝ≥0) : ∀ᵐ w ∂μ,‖polynomialProcess (p n) (clippedClock t (exitTime R) w) w‖≤M := by
    filter_upwards [exit_bounded_ae R R.coe_nonneg t] with w hw
    exact hb n _ hw
  have hmart : Martingale G augmentedJoint μ := by
    refine ⟨had,?_⟩
    intro s t hst
    have hfg (n : ℕ) :
        μ[fun w => polynomialProcess (p n) (clippedClock t (exitTime R) w) w | augmentedJoint s] =ᵐ[μ]
        μ[fun w => polynomialProcess (p n) (clippedClock s (exitTime R) w) w | augmentedJoint s] := by
      have he := clipped_condExp (polynomialProcess (p n)) (polynomialProcess_martingale (p n))
        (polynomialProcess_continuous (p n)) (exitTime R) (exitTime_stopping R) s t hst
      have hfix := condExp_of_stronglyMeasurable (augmented_joint_le s)
        (clipped_adapted (polynomialProcess (p n)) (polynomialProcess_stronglyAdapted (p n))
          (polynomialProcess_continuous (p n)) (exitTime R) (exitTime_stopping R) s) (hpolyint n s)
      rw [hfix]
      exact he
    have hh := tendsto_condExp_unique (μ := μ) (m := augmentedJoint s)
      (fun n w => polynomialProcess (p n) (clippedClock t (exitTime R) w) w)
      (fun n w => polynomialProcess (p n) (clippedClock s (exitTime R) w) w)
      (G t) (G s) (fun n => hpolyint n t) (fun n => hpolyint n s) (hlim t) (hlim s)
      (fun _ => M) (integrable_const M) (fun _ => M) (integrable_const M)
      (fun n => hpb n t) (fun n => hpb n s) hfg
    rw [condExp_of_stronglyMeasurable (augmented_joint_le s) (had s) (hint s)] at hh
    exact hh
  refine ⟨G,hmart,?_,hactual,M,hM,hbound⟩
  intro w
  exact g.continuous.comp ((value_continuous w).comp (clock_continuous (exitTime R) w))

/-- An actual process on the ORIGINAL probability space and filtration. -/
def process (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) : ℝ≥0 → Sample → ℂ :=
  Classical.choose (exists_stopped_martingale f R S hRS hf)

theorem process_spec (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) :
    Martingale (process f R S hRS hf) augmentedJoint μ ∧
      (∀ w,Continuous (fun t => process f R S hRS hf t w)) ∧
      (∀ t,process f R S hRS hf t =ᵐ[μ] fun w => f (value (clippedClock t (exitTime R) w) w)) ∧
      ∃ M : ℝ,0≤M ∧ ∀ t,∀ᵐ w ∂μ,‖process f R S hRS hf t w‖≤M :=
  Classical.choose_spec (exists_stopped_martingale f R S hRS hf)

/-- The already verified native operator identity belongs to this ACTUAL
continuous martingale version, on the same sample space at every horizon. -/
theorem native_process_identity (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) (T : ℝ≥0) :
    StochasticCauchyComplexChannels.channel T false (((Real.sqrt 2:ℝ):ℂ) •
      StochasticCauchyAnalyticDisk.nativeInput f R S hRS hf T) =ᵐ[μ]
        fun w => process f R S hRS hf T w-f 0 := by
  filter_upwards [StochasticCauchyAnalyticDisk.nativeInput_actual f R S hRS hf T,
    (process_spec f R S hRS hf).2.2.1 T] with w hi hp
  rw [hi,hp]

/-- Genuine uniform integrability over ALL deterministic times, obtained from
the proved common AE bound on this actual continuous martingale version. -/
theorem process_uniformIntegrable (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) :
    UniformIntegrable (process f R S hRS hf) 1 μ := by
  obtain ⟨M,hM,hb⟩ := (process_spec f R S hRS hf).2.2.2
  have hm (t : ℝ≥0) : AEStronglyMeasurable (process f R S hRS hf t) μ :=
    (((process_spec f R S hRS hf).1.stronglyAdapted t).mono (augmented_joint_le t)).aestronglyMeasurable
  apply uniformIntegrable_of (by norm_num) (by norm_num) hm
  intro ε hε
  let C : ℝ≥0 := ⟨M+1,by linarith⟩
  refine ⟨C,?_⟩
  intro t
  have he : {w | C≤‖process f R S hRS hf t w‖₊}.indicator (process f R S hRS hf t) =ᵐ[μ] fun _ => (0:ℂ) := by
    filter_upwards [hb t] with w hw
    apply Set.indicator_of_notMem
    have hn : ‖process f R S hRS hf t w‖₊<C := by
      change ‖process f R S hRS hf t w‖<(M+1:ℝ)
      linarith
    exact not_le_of_gt hn
  rw [eLpNorm_congr_ae he]
  change eLpNorm (0 : Sample → ℂ) 1 μ≤ε
  rw [eLpNorm_zero]
  exact le_of_lt hε

/-- ACTUAL terminal conditional reconstruction in the ORIGINAL deterministic
past. This is not just equality of single-time means or a stopped-space law. -/
theorem process_closed_by_exit (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) (T : ℝ≥0) :
    μ[fun w => f (StochasticCauchyExitOccupation.exitValue R w) | augmentedJoint T] =ᵐ[μ]
      process f R S hRS hf T := by
  obtain ⟨hm,hc,ha,M,hM,hb⟩ := process_spec f R S hRS hf
  have hlim : ∀ᵐ w ∂μ,Tendsto (fun n : ℕ => process f R S hRS hf (n+⌈T⌉₊) w) atTop
      (𝓝 (f (StochasticCauchyExitOccupation.exitValue R w))) := by
    filter_upwards [ae_all_iff.mpr (fun n : ℕ => ha (n+⌈T⌉₊)),exit_clock_eventually R R.coe_nonneg] with w haw hclock
    have hs : ∀ᶠ n : ℕ in atTop,clippedClock (n+⌈T⌉₊) (exitTime R) w=StochasticCauchyExitOccupation.finiteExit R w :=
      by simpa only [Nat.cast_add] using (tendsto_add_atTop_nat ⌈T⌉₊).eventually hclock
    have heq : (fun n : ℕ => process f R S hRS hf (n+⌈T⌉₊) w) =ᶠ[atTop]
        fun _ => f (StochasticCauchyExitOccupation.exitValue R w) := hs.mono fun n hn => by
      change process f R S hRS hf (n+⌈T⌉₊) w=f (StochasticCauchyExitOccupation.exitValue R w)
      rw [haw n]
      change f (value (clippedClock (n+⌈T⌉₊) (exitTime R) w) w)=_
      rw [hn]
      rfl
    exact (tendsto_congr' heq).mpr tendsto_const_nhds
  have hfix := condExp_of_stronglyMeasurable (augmented_joint_le T) (hm.stronglyAdapted T) (hm.integrable T)
  have hfg (n : ℕ) : μ[process f R S hRS hf (n+⌈T⌉₊) | augmentedJoint T] =ᵐ[μ]
      μ[process f R S hRS hf T | augmentedJoint T] := by
    rw [hfix]
    apply hm.2
    exact (Nat.le_ceil T).trans (by exact_mod_cast (Nat.le_add_left ⌈T⌉₊ n))
  have hh := tendsto_condExp_unique (μ := μ) (m := augmentedJoint T)
    (fun n : ℕ => process f R S hRS hf (n+⌈T⌉₊)) (fun _ : ℕ => process f R S hRS hf T)
    (fun w => f (StochasticCauchyExitOccupation.exitValue R w)) (process f R S hRS hf T)
    (fun n => hm.integrable _) (fun _ => hm.integrable T) hlim
    (Eventually.of_forall fun _ => tendsto_const_nhds)
    (fun _ => M) (integrable_const M) (fun _ => M) (integrable_const M)
    (fun n => hb _) (fun _ => hb T) hfg
  rwa [hfix] at hh

end OperatorDerivativeRewrite.Foundation.StochasticCauchyAnalyticMartingale
