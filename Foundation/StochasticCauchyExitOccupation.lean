import Foundation.StochasticCauchyExitClock
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-! Exact native stopped-indicator occupation and finite radial exit. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyExitOccupation
open InfiniteGaussian StochasticCauchyStoppedDomains StochasticCauchyExitClock
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyPhysicalInput StochasticCauchyExponentialInput StochasticCauchyPastReconstruction
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct
variable (τ : Sample → WithTop ℝ≥0) (hτ : IsStoppingTime augmentedJoint τ)

/-- Actual real-valued bounded clock, not an a.s.finite substitute for tau. -/
def clockValue (T : ℝ≥0) (w : Sample) : ℝ := clippedClock T τ w

include hτ in
theorem clockValue_measurable (T : ℝ≥0) : Measurable (clockValue τ T) := by
  have hm : Measurable (clippedClock T τ) :=
    (WithTop.measurable_untopD 0).comp (hτ.min_const T).measurable'
  exact NNReal.continuous_coe.measurable.comp hm

include hτ in
theorem clockValue_integrable (T : ℝ≥0) : Integrable (clockValue τ T) μ := by
  apply Integrable.mono' (integrable_const (T:ℝ)) (clockValue_measurable τ hτ T).aestronglyMeasurable
  exact Eventually.of_forall fun w => by
    simp only [clockValue,Real.norm_eq_abs,abs_of_nonneg (clippedClock T τ w).coe_nonneg]
    exact_mod_cast clippedClock_le T τ w

private def survivalClass (T : ℝ≥0) (r : ℝ) : JointL2 :=
  indicatorConstLp 2 (measurableSet_le (measurable_const (a := r)) (clockValue_measurable τ hτ T))
    (measure_ne_top μ _) (1:ℝ)

private theorem survivalClass_actual (T : ℝ≥0) (r : ℝ) :
    survivalClass τ hτ T r =ᵐ[μ] {w | r≤clockValue τ T w}.indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn

private theorem survivalClass_norm (T : ℝ≥0) (r : ℝ) :
    ‖survivalClass τ hτ T r‖^2=μ.real {w | r≤clockValue τ T w} := by
  rw [survivalClass,norm_indicatorConstLp (by norm_num) (by norm_num)]
  norm_num only [norm_one,one_mul,ENNReal.toReal_ofNat]
  rw [← Real.sqrt_eq_rpow,Real.sq_sqrt (measureReal_nonneg)]

private theorem native_slices (T : ℝ≥0) :
    ∀ᵐ r ∂timeLaw T,timeSections T (fieldEmbedding T (stoppedInput T τ hτ)) r=survivalClass τ hτ T r := by
  have hp := StochasticCauchyStoppedIndicators.stoppedInput_physical (clippedClock T τ)
    (clippedClock_stopping T τ hτ) T
  filter_upwards [timeSections_ae T (fieldEmbedding T (stoppedInput T τ hτ)),hp,
    ae_restrict_mem (μ := volume) measurableSet_Ioc] with r hs hp hin
  apply Lp.ext
  filter_upwards [hs,hp,survivalClass_actual τ hτ T r] with w hs hp hc
  change fieldEmbedding T (stoppedInput T τ hτ) ((r,w.1),w.2)=_ at hp
  rw [hs,hp,hc]
  simp only [Set.indicator,Set.mem_Ioc,Set.mem_ofPred_eq,hin.1,true_and,clockValue]
  rfl

/-- EXACT occupation identity on the original native domain, for every
possibly infinite stopping time and every deterministic horizon including0. -/
theorem stopped_occupation (T : ℝ≥0) :
    ‖stoppedInput T τ hτ‖^2=∫ w,clockValue τ T w ∂μ := by
  have hn : ‖stoppedInput T τ hτ‖^2=
      ∫ r,‖timeSections T (fieldEmbedding T (stoppedInput T τ hτ)) r‖^2 ∂timeLaw T := by
    rw [← (fieldEmbedding T).norm_map (stoppedInput T τ hτ),
      ← (timeSections T).norm_map (fieldEmbedding T (stoppedInput T τ hτ)),BochnerL2Dominated.norm_sq_integral]
  calc
    ‖stoppedInput T τ hτ‖^2 = ∫ r,‖timeSections T (fieldEmbedding T (stoppedInput T τ hτ)) r‖^2 ∂timeLaw T := hn
    _ = ∫ r,μ.real {w | r≤clockValue τ T w} ∂timeLaw T := by
      apply integral_congr_ae
      filter_upwards [native_slices τ hτ T] with r hr
      rw [hr,survivalClass_norm]
    _ = ∫ w,clockValue τ T w ∂μ :=
      ((clockValue_integrable τ hτ T).integral_eq_integral_Ioc_meas_le
        (Eventually.of_forall fun w => (clippedClock T τ w).coe_nonneg)
        (Eventually.of_forall fun w => show clockValue τ T w≤(T:ℝ) from clippedClock_le T τ w)).symm

/-- The actual expected truncated radial exit time is bounded uniformly inT. -/
theorem exit_clock_bound (R : ℝ) (hR : 0≤R) (T : ℝ≥0) :
    (∫ w,clockValue (exitTime R) T w ∂μ)≤R^2/2 := by
  rw [← stopped_occupation (exitTime R) (exitTime_stopping R) T]
  exact exit_input_energy R hR T

/-- The SAME actual exit clock, with the existing ENNReal type made explicit. -/
def exitDuration (R : ℝ) (w : Sample) : ℝ≥0∞ := exitTime R w

private theorem truncated_form (R : ℝ) (n : ℕ) (w : Sample) :
    ENNReal.ofReal (clockValue (exitTime R) n w)=min (exitDuration R w) (n:ℝ≥0∞) := by
  cases he : exitTime R w with
  | top =>
    have hc : clippedClock n (exitTime R) w=(n:ℝ≥0) := by
      apply WithTop.coe_injective
      rw [clippedClock_coe,he,min_eq_right le_top]
    rw [clockValue,hc,ENNReal.ofReal_coe_nnreal,ENNReal.coe_natCast]
    have hd : exitDuration R w=∞ := he
    rw [hd]
    change (n:ℝ≥0∞)=min (⊤:ℝ≥0∞) n
    exact (min_eq_right le_top).symm
  | coe t =>
    have hc : clippedClock n (exitTime R) w=min t (n:ℝ≥0) := by
      apply WithTop.coe_injective
      rw [clippedClock_coe,he,WithTop.coe_min]
    have hd : exitDuration R w=(t:ℝ≥0∞) := he
    rw [clockValue,hc,hd,ENNReal.ofReal_coe_nnreal,ENNReal.coe_min,ENNReal.coe_natCast]

/-- Genuine expected exit-time bound, including control of a potentially
infinite clock. The integral is the actual nonnegative Lebesgue integral. -/
theorem exit_lintegral_bound (R : ℝ) (hR : 0≤R) :
    (∫⁻ w,exitDuration R w ∂μ)≤ENNReal.ofReal (R^2/2) := by
  let F : ℕ → Sample → ℝ≥0∞ := fun n w => ENNReal.ofReal (clockValue (exitTime R) n w)
  have hm (n : ℕ) : Measurable (F n) :=
    (clockValue_measurable (exitTime R) (exitTime_stopping R) n).ennreal_ofReal
  have hmono : Monotone F := by
    intro m n hmn w
    dsimp only [F]
    rw [truncated_form,truncated_form]
    exact min_le_min_left _ (by exact_mod_cast hmn)
  have hs (w : Sample) : (⨆ n,F n w)=exitDuration R w := by
    simp only [F,truncated_form]
    rw [← inf_iSup_eq,ENNReal.iSup_natCast,inf_top_eq]
  calc
    (∫⁻ w,exitDuration R w ∂μ) = ∫⁻ w,⨆ n,F n w ∂μ := by
      apply lintegral_congr
      intro w;exact (hs w).symm
    _ = ⨆ n,∫⁻ w,F n w ∂μ := lintegral_iSup hm hmono
    _ ≤ ENNReal.ofReal (R^2/2) := by
      apply iSup_le
      intro n
      dsimp only [F]
      rw [← ofReal_integral_eq_lintegral_ofReal
        (clockValue_integrable (exitTime R) (exitTime_stopping R) n)
        (Eventually.of_forall fun w => (clippedClock n (exitTime R) w).coe_nonneg)]
      exact ENNReal.ofReal_le_ofReal (exit_clock_bound R hR n)

/-- The CONSTRUCTED continuous radial first exit is genuinely finite AE,
proved from native occupation and energy rather than assumed. -/
theorem exit_finite_ae (R : ℝ) (hR : 0≤R) : ∀ᵐ w ∂μ,exitTime R w≠⊤ := by
  have hi : (∫⁻ w,exitDuration R w ∂μ)<∞ :=
    (exit_lintegral_bound R hR).trans_lt ENNReal.ofReal_lt_top
  have hm : Measurable (exitDuration R) := (exitTime_stopping R).measurable'
  filter_upwards [ae_lt_top hm hi.ne] with w hw
  intro he
  have ht : exitDuration R w=∞ := he
  exact (ne_of_lt hw) ht

/-- A real duration is used only AFTER the actual extended clock has been
proved finite AE. Its value0 on the null top event is explicit. -/
def realDuration (R : ℝ) (w : Sample) : ℝ := (exitDuration R w).toReal

theorem realDuration_integrable (R : ℝ) (hR : 0≤R) : Integrable (realDuration R) μ :=
  integrable_toReal_of_lintegral_ne_top (exitTime_stopping R).measurable'.aemeasurable
    ((exit_lintegral_bound R hR).trans_lt ENNReal.ofReal_lt_top).ne

theorem realDuration_bound (R : ℝ) (hR : 0≤R) : (∫ w,realDuration R w ∂μ)≤R^2/2 := by
  have he : (∫ w,realDuration R w ∂μ)=(∫⁻ w,exitDuration R w ∂μ).toReal :=
    integral_toReal (exitTime_stopping R).measurable'.aemeasurable (by
      filter_upwards [exit_finite_ae R hR] with w hw
      exact lt_top_iff_ne_top.mpr hw)
  rw [he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (exit_lintegral_bound R hR)).trans
    (le_of_eq (ENNReal.toReal_ofReal (by positivity)))

def finiteExit (R : ℝ) (w : Sample) : ℝ≥0 := (exitTime R w).untopD 0

theorem finiteExit_measurable (R : ℝ) : Measurable (finiteExit R) :=
  (WithTop.measurable_untopD 0).comp (exitTime_stopping R).measurable'

theorem finiteExit_actual (R : ℝ) (hR : 0≤R) : ∀ᵐ w ∂μ,(finiteExit R w:WithTop ℝ≥0)=exitTime R w := by
  filter_upwards [exit_finite_ae R hR] with w hw
  cases he : exitTime R w with
  | top => exact False.elim (hw he)
  | coe t => simp only [finiteExit,he,WithTop.untopD_coe]

/-- Actual path evaluation at the finite version of the TRUE exit clock. -/
def exitValue (R : ℝ) (w : Sample) : ℂ := StochasticCauchyBrownianRealization.value (finiteExit R w) w

private theorem sample_clock_measurable (c : Sample → ℝ≥0) (hc : Measurable c) :
    Measurable (fun w : Sample => StochasticCauchyBrownianRealization.value (c w) w) :=
  Measurable.comp
    (g := fun p : ℝ≥0 × Sample => StochasticCauchyBrownianRealization.value p.1 p.2)
    (f := fun w : Sample => (c w,w))
    StochasticCauchyBrownianRealization.value_jointly_measurable (hc.prodMk measurable_id)

theorem exitValue_measurable (R : ℝ) : Measurable (exitValue R) :=
  sample_clock_measurable (finiteExit R) (finiteExit_measurable R)

theorem exitValue_boundary (R : ℝ) (hR : 0≤R) : ∀ᵐ w ∂μ,‖exitValue R w‖=R := by
  filter_upwards [finiteExit_actual R hR,StochasticCauchyBrownianRealization.value_zero_ae] with w ht hz
  exact exit_boundary R w (finiteExit R w) (by simpa only [hz,norm_zero] using hR) ht.symm

theorem exitValue_memLp (R : ℝ) (hR : 0≤R) : MemLp (exitValue R) 2 μ :=
  MemLp.of_bound (exitValue_measurable R).aestronglyMeasurable R
    ((exitValue_boundary R hR).mono fun _ hw => hw.le)

private theorem clipped_eventually (R : ℝ) (w : Sample)
    (hw : (finiteExit R w:WithTop ℝ≥0)=exitTime R w) :
    ∀ᶠ n : ℕ in atTop,clippedClock n (exitTime R) w=finiteExit R w := by
  have hn : ∀ᶠ n : ℕ in atTop,finiteExit R w≤(n:ℝ≥0) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  exact hn.mono fun n hn => by
    apply WithTop.coe_injective
    rw [clippedClock_coe,← hw,min_eq_left (WithTop.coe_le_coe.mpr hn)]

private theorem sampled_tendsto (R : ℝ) (hR : 0≤R) : ∀ᵐ w ∂μ,
    Tendsto (fun n : ℕ => StochasticCauchyBrownianRealization.value (clippedClock n (exitTime R) w) w)
      atTop (𝓝 (exitValue R w)) := by
  filter_upwards [finiteExit_actual R hR] with w hw
  exact (tendsto_congr' ((clipped_eventually R w hw).mono fun n hn => by rw [hn];rfl)).mpr tendsto_const_nhds

open StochasticCauchyComplexChannels ComplexL2Isometry

def exitClass (R : ℝ) (hR : 0≤R) : JointComplex := (exitValue_memLp R hR).toLp (exitValue R)

theorem exitClass_actual (R : ℝ) (hR : 0≤R) : exitClass R hR =ᵐ[μ] exitValue R := MemLp.coeFn_toLp _

/-- The ACTUAL bounded-horizon integrals converge strongly to the genuine
untruncated exit observable. No common infinite-horizon input space is assumed. -/
theorem native_exit_tendsto (R : ℝ) (hR : 0≤R) :
    Tendsto (fun n : ℕ => channel n false (exitComplexInput R n)) atTop (𝓝 (exitClass R hR)) := by
  let b : JointL2 := R • jointOne
  have hb : b =ᵐ[μ] fun _ => R := by
    filter_upwards [Lp.coeFn_smul R jointOne,jointOne_ae] with w hs h1
    simp only [b,hs,Pi.smul_apply,h1,smul_eq_mul,mul_one]
  apply BochnerL2Approximation.tendsto_of_dominated _ _ b
  · intro n
    filter_upwards [exit_stochastic_actual R n,exit_bounded_ae R hR n,hb] with w hi hn hb
    rw [hi,hb,Real.norm_eq_abs,abs_of_nonneg hR];exact hn
  · filter_upwards [exitClass_actual R hR,exitValue_boundary R hR,hb] with w hv hn hb
    rw [hv,hn,hb,Real.norm_eq_abs,abs_of_nonneg hR]
  · filter_upwards [ae_all_iff.mpr (fun n : ℕ => exit_stochastic_actual R n),
      exitClass_actual R hR,sampled_tendsto R hR] with w hi he ht
    simpa only [hi,he] using ht

/-- Actual untruncated exit has mean0, obtained by a valid bounded limit. -/
theorem exitValue_mean_zero (R : ℝ) (hR : 0≤R) : (∫ w,exitValue R w ∂μ)=0 := by
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Sample => R)
    (fun n : ℕ => (exit_memLp R n).aestronglyMeasurable) (integrable_const R)
    (fun n : ℕ => exit_bounded_ae R hR n) (sampled_tendsto R hR)
  simp only [exit_mean_zero] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem native_exit_mean_square (R : ℝ) (hR : 0≤R) :
    Tendsto (fun n : ℕ => ∫ w,‖StochasticCauchyBrownianRealization.value (clippedClock n (exitTime R) w) w-
      exitValue R w‖^2 ∂μ) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ‖channel n false (exitComplexInput R n)-exitClass R hR‖^2) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using
      (((native_exit_tendsto R hR).sub_const (exitClass R hR)).norm.pow 2)
  have he (n : ℕ) : ‖channel n false (exitComplexInput R n)-exitClass R hR‖^2=
      ∫ w,‖StochasticCauchyBrownianRealization.value (clippedClock n (exitTime R) w) w-exitValue R w‖^2 ∂μ := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (channel n false (exitComplexInput R n)) (exitClass R hR),
      exit_stochastic_actual R n,exitClass_actual R hR] with w hs hi he
    simp only [hs,Pi.sub_apply,hi,he]
  simpa only [he] using hn

private theorem duration_actual (R : ℝ) (hR : 0≤R) :
    realDuration R =ᵐ[μ] fun w => (finiteExit R w:ℝ) := by
  filter_upwards [finiteExit_actual R hR] with w hw
  have he : exitDuration R w=(finiteExit R w:ℝ≥0∞) := hw.symm
  simpa only [realDuration,ENNReal.coe_toReal] using congrArg ENNReal.toReal he

private theorem expected_clock_tendsto (R : ℝ) (hR : 0≤R) :
    Tendsto (fun n : ℕ => ∫ w,clockValue (exitTime R) n w ∂μ) atTop (𝓝 (∫ w,realDuration R w ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (realDuration R)
    (fun n : ℕ => (clockValue_measurable (exitTime R) (exitTime_stopping R) n).aestronglyMeasurable)
    (realDuration_integrable R hR)
  · intro n
    filter_upwards [finiteExit_actual R hR,duration_actual R hR] with w hw hd
    have hle : clippedClock n (exitTime R) w≤finiteExit R w := by
      apply WithTop.coe_le_coe.mp
      rw [clippedClock_coe,← hw]
      exact min_le_left _ _
    simp only [clockValue,Real.norm_eq_abs,abs_of_nonneg (clippedClock n (exitTime R) w).coe_nonneg,hd]
    exact_mod_cast hle
  · filter_upwards [finiteExit_actual R hR,duration_actual R hR] with w hw hd
    have he : (fun n : ℕ => clockValue (exitTime R) n w) =ᶠ[atTop] fun _ => realDuration R w :=
      (clipped_eventually R w hw).mono fun n hn => by simp only [clockValue,hn,hd]
    exact (tendsto_congr' he).mpr tendsto_const_nhds

private theorem output_energy (R : ℝ) (T : ℝ≥0) :
    ‖channel T false (exitComplexInput R T)‖^2=2*(∫ w,clockValue (exitTime R) T w ∂μ) := by
  have hp := StochasticCauchyStoppedIndicators.stoppedInput_parts (clippedClock T (exitTime R))
    (clippedClock_stopping T (exitTime R) (exitTime_stopping R)) T
  change ‖channel T false (StochasticCauchyStoppedIndicators.stoppedComplexInput
    (clippedClock T (exitTime R)) (clippedClock_stopping T (exitTime R) (exitTime_stopping R)) T)‖^2=_
  rw [(channel T false).norm_map,input_norm_sq,hp.1,hp.2,norm_smul]
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg 2),mul_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ)≤2),norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),add_zero]
  change 2*‖stoppedInput T (exitTime R) (exitTime_stopping R)‖^2=_
  rw [stopped_occupation]

theorem exitClass_norm_sq (R : ℝ) (hR : 0≤R) : ‖exitClass R hR‖^2=R^2 := by
  rw [BochnerL2Dominated.norm_sq_integral]
  calc
    (∫ w,‖exitClass R hR w‖^2 ∂μ) = ∫ _ : Sample,R^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [exitClass_actual R hR,exitValue_boundary R hR] with w hv hb
      rw [hv,hb]
    _ = R^2 := by simp

/-- SHARP actual expected first-exit time for the existing two standard
Brownian coordinates: E tau_R = R^2/2. -/
theorem expected_exit_time (R : ℝ) (hR : 0≤R) : (∫ w,realDuration R w ∂μ)=R^2/2 := by
  have hv := (native_exit_tendsto R hR).norm.pow 2
  rw [exitClass_norm_sq] at hv
  have ht : Tendsto (fun n : ℕ => 2*(∫ w,clockValue (exitTime R) n w ∂μ)) atTop
      (𝓝 (2*(∫ w,realDuration R w ∂μ))) := tendsto_const_nhds.mul (expected_clock_tendsto R hR)
  simp only [output_energy] at hv
  have he := tendsto_nhds_unique hv ht
  linarith

/-- A genuine nonconstant circle-supported exit observable; no uniform
circle law or full Gaussian derivative domain is assumed. -/
theorem exitValue_nonconstant (R : ℝ) (hR : 0<R) :
    ¬∃ c : ℂ,exitValue R =ᵐ[μ] fun _ => c := by
  rintro ⟨c,hc⟩
  have hm := integral_congr_ae hc
  rw [exitValue_mean_zero R hR.le] at hm
  simp only [integral_const,probReal_univ,one_smul] at hm
  have hz : c=0 := hm.symm
  have hh : ∀ᵐ w ∂μ,R=0 := by
    filter_upwards [exitValue_boundary R hR.le,hc] with w hb hc
    rw [hc,hz,norm_zero] at hb
    exact hb.symm
  obtain ⟨w,hw⟩ := hh.exists
  exact hR.ne' hw

end OperatorDerivativeRewrite.Foundation.StochasticCauchyExitOccupation
