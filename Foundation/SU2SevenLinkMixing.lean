import Foundation.YMPositiveMixing
import Foundation.SU2SevenLinkIteration

/-! Actual finite-coupling mixing by the positive ground-state bridge.
No physical spacing or homogeneous four-dimensional identification is assumed. -/
noncomputable section
open MeasureTheory Filter
namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkMixing
open SU2SevenLinkTransfer SU2SevenLinkGroundTransform SU2SevenLinkL2Transfer
open SU2SevenLinkVacuum
variable {β t : ℝ} (d : GroundData β t)

private theorem function_integrable : Integrable d.function haar :=
  Integrable.of_bound d.measurable.aestronglyMeasurable d.upper
    (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using (d.bounds y).2)

private theorem function_mass_pos :
    0 < SignedDensityProbabilitySampling.mass haar d.function := by
  have he := integral_mono (integrable_const d.lower) (function_integrable d)
    (fun y => (d.bounds y).1)
  have hh : d.lower ≤ ∫ y,d.function y ∂haar := by simpa using he
  unfold SignedDensityProbabilitySampling.mass
  simp_rw [abs_of_pos (d.function_pos _)]
  exact d.lower_pos.trans_le hh

/-- This reference is psi*dHaar normalized; the stationary law is psi^2*dHaar.
They are deliberately NOT identified. -/
def bridgeReference : Measure State := SignedDensityProbabilitySampling.sampler haar d.function

theorem bridgeReference_probability : IsProbabilityMeasure (bridgeReference d) :=
  SignedDensityProbabilitySampling.sampler_probability haar d.function
    (function_integrable d) (function_mass_pos d)

theorem transfer_bridge (f : State → ℝ) (hf : Measurable f) (s : State) :
    transfer d f s=YMPositiveKernel.average (bridgeReference d) (kernelDensity β t) f s := by
  have hground (y : State) : YMPositiveKernel.sandwich haar (fun _ => 1)
      (kernelDensity β t) d.function y=d.value*d.function y := by
    simpa only [YMPositiveKernel.sandwich,one_mul,mul_one,YMPositivePower.applyKernel]
      using (kernelDensity_apply β t d.function y).trans (d.eigen y)
  have he := YMPositiveKernel.ground_bridge haar (fun _ => 1) d.function
    (kernelDensity β t) d.value (by simpa only [one_mul] using d.measurable)
    (fun _ => by norm_num) d.function_pos d.value_pos
    (by simpa only [one_mul] using function_mass_pos d) hground f s
  rw [transfer,d.kernel_integral f hf]
  simp only [bridgeReference,one_mul] at he ⊢
  rw [← he]
  congr 1
  simpa only [YMPositiveKernel.sandwich,one_mul,mul_one,YMPositivePower.applyKernel]
    using (kernelDensity_apply β t (fun y => d.function y*f y) s).symm

theorem nativeSteps_mean (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s,|f s| ≤ B) (n : ℕ) :
    (∫ s,nativeSteps d n f s ∂d.stationary)=∫ s,f s ∂d.stationary := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∫ s,∫ r,nativeSteps d n f r ∂d.kernel s ∂d.stationary)=_
    rw [d.kernel_stationary _ (nativeSteps_measurable d n f hf) B
      (nativeSteps_bound d n f B hb)]
    exact ih

/-- Uniform in the starting state, for every bounded centered native probe. -/
theorem nativeSteps_centered_bound (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s,|f s| ≤ B) (hzero : (∫ s,f s ∂d.stationary)=0)
    (n : ℕ) (s : State) :
    |nativeSteps d n f s| ≤ 2*B*(1-lower β t/upper β t)^n := by
  letI : IsProbabilityMeasure (bridgeReference d) := bridgeReference_probability d
  letI : IsProbabilityMeasure d.stationary := d.stationary_probability
  exact YMPositiveMixing.centered_iterate_bound (bridgeReference d) d.stationary
    (kernelDensity β t) (lower β t) (upper β t) (kernelDensity_measurable β t)
    (lower_pos β t) (kernelDensity_bounds β t) (fun n => nativeSteps d n f)
    (fun n => nativeSteps_measurable d n f hf)
    (fun n x => transfer_bridge d _ (nativeSteps_measurable d n f hf) x)
    (fun n => (nativeSteps_mean d f hf B hb n).trans hzero) B hb n s

/-- Exact cancellation of all seven Wilson partition factors. -/
theorem reset_ratio (β t : ℝ) : lower β t/upper β t=Real.exp (-2*|t|-14*|β|) := by
  let Z := BoundedExponentialTiltResponse.partition QuaternionSU2Representation.law
    QuaternionSU2Representation.halfTrace β
  have hz : 0 < Z := BoundedExponentialTiltResponse.partition_pos _ _
    QuaternionSU2Representation.halfTrace_measurable QuaternionSU2Representation.halfTrace_bound β
  have hL : lower β t=Real.exp (-|t|-7*|β|)/Z^7 := by
    unfold lower
    rw [div_pow,← Real.exp_nat_mul,← Real.exp_nat_mul,← mul_div_assoc,← Real.exp_add]
    congr 1
    ring
  have hU : upper β t=Real.exp (|t|+7*|β|)/Z^7 := by
    unfold upper
    rw [div_pow,← Real.exp_nat_mul,← Real.exp_nat_mul,← mul_div_assoc,← Real.exp_add]
    congr 1
    ring
  rw [hL,hU,div_div_div_cancel_right₀ (pow_ne_zero 7 hz.ne'),← Real.exp_sub]
  congr 1
  ring

def reset (β t : ℝ) : ℝ := Real.exp (-2*|t|-14*|β|)

theorem reset_bounds (β t : ℝ) : 0 < reset β t ∧ reset β t ≤ 1 := by
  exact ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg t,abs_nonneg β])⟩

/-- Exponential upper bound on the actual native stationary covariance. -/
theorem native_covariance_bound (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s,|f s| ≤ B) (hzero : (∫ s,f s ∂d.stationary)=0) (n : ℕ) :
    |∫ s,f s*nativeSteps d n f s ∂d.stationary| ≤ 2*B^2*(1-reset β t)^n := by
  letI : IsProbabilityMeasure d.stationary := d.stationary_probability
  have hB : 0 ≤ B := (abs_nonneg (f 1)).trans (hb 1)
  have hθ : 0 ≤ 1-reset β t := sub_nonneg.mpr (reset_bounds β t).2
  have hpoint (s : State) := nativeSteps_centered_bound d f hf B hb hzero n s
  simp_rw [reset_ratio] at hpoint
  have he := norm_integral_le_of_norm_le_const (μ := d.stationary)
    (f := fun s => f s*nativeSteps d n f s) (C := 2*B^2*(1-reset β t)^n)
    (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs,abs_mul]
      calc
        _ ≤ B*(2*B*(1-reset β t)^n) :=
          mul_le_mul (hb s) (hpoint s) (abs_nonneg _) hB
        _ = _ := by ring)
  simpa only [Real.norm_eq_abs,probReal_univ,one_mul,mul_one] using he

theorem native_covariance_tendsto_zero (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s,|f s| ≤ B) (hzero : (∫ s,f s ∂d.stationary)=0) :
    Tendsto (fun n : ℕ => ∫ s,f s*nativeSteps d n f s ∂d.stationary) atTop (nhds 0) := by
  have hθ0 : 0 ≤ 1-reset β t := sub_nonneg.mpr (reset_bounds β t).2
  have hθ1 : 1-reset β t < 1 := by linarith [(reset_bounds β t).1]
  have hlim : Tendsto (fun n : ℕ => 2*B^2*(1-reset β t)^n) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1)
  apply squeeze_zero_norm _ hlim
  intro n
  simpa only [Real.norm_eq_abs] using (native_covariance_bound d f hf B hb hzero n)

theorem reset_power_exp_bound (β t : ℝ) (n : ℕ) :
    (1-reset β t)^n ≤ Real.exp (-(n:ℝ)*reset β t) := by
  have hbase : 1-reset β t ≤ Real.exp (-reset β t) := by
    linarith [Real.add_one_le_exp (-reset β t)]
  have he := pow_le_pow_left₀ (sub_nonneg.mpr (reset_bounds β t).2) hbase n
  have hp : Real.exp (-reset β t)^n=Real.exp (-(n:ℝ)*reset β t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [hp] at he

/-- A sufficient coupling-dependent count; the prefactor remains explicit. -/
theorem native_covariance_macro_bound (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s,|f s| ≤ B) (hzero : (∫ s,f s ∂d.stationary)=0)
    (r : ℝ) (n : ℕ) (hn : r ≤ (n:ℝ)*reset β t) :
    |∫ s,f s*nativeSteps d n f s ∂d.stationary| ≤ 2*B^2*Real.exp (-r) := by
  refine (native_covariance_bound d f hf B hb hzero n).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (reset_power_exp_bound β t n).trans (Real.exp_le_exp.mpr (by linarith))

theorem sufficient_step_count (β t r : ℝ) (n : ℕ)
    (hn : r*Real.exp (2*|t|+14*|β|) ≤ (n:ℝ)) : r ≤ (n:ℝ)*reset β t := by
  have he : (r*Real.exp (2*|t|+14*|β|))*reset β t=r := by
    unfold reset
    rw [mul_assoc,← Real.exp_add]
    have hz : 2*|t|+14*|β|+(-2*|t|-14*|β|)=0 := by ring
    rw [hz,Real.exp_zero,mul_one]
  rw [← he]
  exact mul_le_mul_of_nonneg_right hn (reset_bounds β t).1.le

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkMixing
