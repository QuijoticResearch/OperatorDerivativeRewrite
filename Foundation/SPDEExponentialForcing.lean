import Foundation.SPDECountableModes
import Foundation.SPDEWickModes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Actual exponential convolution profiles and a sharp countable-mode trace criterion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.SPDEExponentialForcing
open GaussianTimeHilbert InfiniteGaussian SPDECountableModes
attribute [local instance] timeHilbert_secondCountable

def response (rate t : ℝ≥0) : ℝ → ℝ :=
  (Ioc 0 (t : ℝ)).indicator (fun s => Real.exp (-(rate : ℝ)*((t : ℝ)-s)))

theorem response_measurable (rate t : ℝ≥0) : Measurable (response rate t) := by
  unfold response
  exact (by fun_prop : Measurable (fun s : ℝ => Real.exp (-(rate : ℝ)*((t : ℝ)-s)))).indicator measurableSet_Ioc

theorem response_memLp (rate t : ℝ≥0) : MemLp (response rate t) 2 volume := by
  apply MemLp.of_le_mul (c := 1) (interval_indicator_memLp 0 t)
    (response_measurable rate t).aestronglyMeasurable
  apply Eventually.of_forall
  intro s
  by_cases hs : s∈Ioc 0 (t : ℝ)
  · simp only [response,indicator_of_mem hs,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      abs_one,one_mul]
    apply Real.exp_le_one_iff.mpr
    simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg rate.coe_nonneg (sub_nonneg.mpr hs.2))
  · simp [response,hs]

def responseVector (rate t : ℝ≥0) : TimeHilbert := (response_memLp rate t).toLp (response rate t)

theorem responseVector_coeFn (rate t : ℝ≥0) : responseVector rate t =ᵐ[volume] response rate t :=
  MemLp.coeFn_toLp _

theorem responseVector_energy (rate t : ℝ≥0) : ‖responseVector rate t‖^2=∫ s, (response rate t s)^2 := by
  rw [← real_inner_self_eq_norm_sq,L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [responseVector_coeFn rate t] with s hs
  simp [hs,Real.inner_apply]

private theorem integral_exp_linear (c t : ℝ) (hc : c≠0) :
    (∫ s in (0 : ℝ)..t, Real.exp (c*s))=(Real.exp (c*t)-1)/c := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => Real.exp (c*r)/c) (Real.exp (c*s)) s := by
    convert (((hasDerivAt_id s).const_mul c).exp.div_const c) using 1 <;> simp [hc,mul_comm]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hd s)
    (show IntervalIntegrable (fun s : ℝ => Real.exp (c*s)) volume 0 t from (by fun_prop : Continuous _).intervalIntegrable _ _)
  simp only [mul_zero,Real.exp_zero] at hi
  rw [hi]
  ring

theorem responseVector_energy_exact (rate t : ℝ≥0) (hrate : 0<rate) :
    ‖responseVector rate t‖^2=(1-Real.exp (-2*(rate : ℝ)*(t : ℝ)))/(2*(rate : ℝ)) := by
  rw [responseVector_energy]
  have he : (fun s => (response rate t s)^2)=
      (Ioc 0 (t : ℝ)).indicator (fun s => Real.exp (-2*(rate : ℝ)*((t : ℝ)-s))) := by
    funext s
    by_cases hs : s∈Ioc 0 (t : ℝ)
    · rw [response,indicator_of_mem hs,indicator_of_mem hs,← Real.exp_nat_mul]
      congr 1
      ring
    · simp [response,hs]
  rw [he,integral_indicator measurableSet_Ioc,← intervalIntegral.integral_of_le t.coe_nonneg]
  have hf : (fun s : ℝ => Real.exp (-2*(rate : ℝ)*((t : ℝ)-s)))=
      fun s => Real.exp (-2*(rate : ℝ)*(t : ℝ))*Real.exp ((2*(rate : ℝ))*s) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hf,intervalIntegral.integral_const_mul,integral_exp_linear (2*(rate : ℝ)) t (by positivity)]
  have hprod : Real.exp (-(2*(rate : ℝ)*(t : ℝ)))*Real.exp ((2*(rate : ℝ))*(t : ℝ))=1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  field_simp
  nlinarith

theorem responseVector_energy_upper (rate t : ℝ≥0) (hrate : 0<rate) :
    ‖responseVector rate t‖^2≤1/(2*(rate : ℝ)) := by
  rw [responseVector_energy_exact rate t hrate]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [Real.exp_pos (-2*(rate : ℝ)*(t : ℝ))]

theorem responseVector_energy_lower (rate t : ℝ≥0) (hrate : 1≤rate) :
    (1-Real.exp (-2*(t : ℝ)))/(2*(rate : ℝ))≤‖responseVector rate t‖^2 := by
  rw [responseVector_energy_exact rate t (by linarith)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have he : Real.exp (-2*(rate : ℝ)*(t : ℝ))≤Real.exp (-2*(t : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [t.coe_nonneg])
  linarith

theorem reciprocal_trace_summable_iff (rate : ℕ → ℝ≥0) (hrate : ∀ n,1≤rate n)
    (c : ℕ → ℝ) (t : ℝ≥0) (ht : 0<t) :
    Summable (fun n => (c n)^2*‖responseVector (rate n) t‖^2) ↔
      Summable (fun n => (c n)^2/(rate n : ℝ)) := by
  let C := 1-Real.exp (-2*(t : ℝ))
  have hC : 0<C := by
    have he : Real.exp (-2*(t : ℝ))<1 := Real.exp_lt_one_iff.mpr (by linarith)
    dsimp [C]
    linarith
  constructor
  · intro hs
    apply (hs.mul_left (2/C)).of_nonneg_of_le (fun n => by positivity)
    intro n
    have hl := responseVector_energy_lower (rate n) t (hrate n)
    have hn : 0<(rate n : ℝ) := by linarith [hrate n]
    have hh := mul_le_mul_of_nonneg_left hl (sq_nonneg (c n))
    change (c n)^2*(C/(2*(rate n : ℝ)))≤(c n)^2*‖responseVector (rate n) t‖^2 at hh
    calc
      _=(2/C)*((c n)^2*(C/(2*(rate n : ℝ)))) := by
        field_simp
      _≤_ := mul_le_mul_of_nonneg_left hh (by positivity)
  · intro hs
    apply (hs.mul_left (1/2 : ℝ)).of_nonneg_of_le (fun n => by positivity)
    intro n
    have hl := responseVector_energy_upper (rate n) t (by linarith [hrate n])
    have hh := mul_le_mul_of_nonneg_left hl (sq_nonneg (c n))
    calc
      _≤(c n)^2*(1/(2*(rate n : ℝ))) := hh
      _=(1/2 : ℝ)*((c n)^2/(rate n : ℝ)) := by ring

theorem actual_series_trace_iff (rate : ℕ → ℝ≥0) (hrate : ∀ n,1≤rate n)
    (c : ℕ → ℝ) (t : ℝ≥0) (ht : 0<t) :
    Summable (fun n => c n • gaussianMode n (responseVector (rate n) t)) ↔
      Summable (fun n => (c n)^2/(rate n : ℝ)) := by
  rw [gaussianSeries_summable_iff,reciprocal_trace_summable_iff rate hrate c t ht]

theorem zero_rate_brownian_profile (t : ℝ≥0) : responseVector 0 t=timeVector t := by
  apply Lp.ext
  filter_upwards [responseVector_coeFn 0 t,timeVector_coeFn t] with s ho hb
  rw [ho,hb]
  simp [response]

def quadraticRates (n : ℕ) : ℝ≥0 := ((n : ℝ≥0)+1)^2
def linearRates (n : ℕ) : ℝ≥0 := (n : ℝ≥0)+1

theorem quadraticRates_lower (n : ℕ) : 1≤quadraticRates n := by
  change (1 : ℝ)≤((n : ℝ)+1)^2
  nlinarith [Nat.cast_nonneg n (α := ℝ)]

theorem quadratic_trace_summable : Summable (fun n => 1/(quadraticRates n : ℝ)) := by
  simpa [quadraticRates,SPDEWickModes.harmonicCoefficient,one_div_pow] using SPDEWickModes.harmonic_square_summable

theorem quadratic_forcing_summable (t : ℝ≥0) :
    Summable (fun n => gaussianMode n (responseVector (quadraticRates n) t)) := by
  have hv : Summable (fun n => ‖responseVector (quadraticRates n) t‖^2) := by
    apply (quadratic_trace_summable.mul_left (1/2 : ℝ)).of_nonneg_of_le (fun n => by positivity)
    intro n
    have hu := responseVector_energy_upper (quadraticRates n) t (by linarith [quadraticRates_lower n])
    simpa only [one_div,mul_inv_rev,mul_comm] using hu
  simpa only [one_smul] using
    (gaussianSeries_summable_iff (fun _ => (1 : ℝ)) (fun n => responseVector (quadraticRates n) t)).mpr
      (by simpa only [one_pow,one_mul] using hv)

theorem linear_forcing_not_summable (t : ℝ≥0) (ht : 0<t) :
    ¬ Summable (fun n => gaussianMode n (responseVector (linearRates n) t)) := by
  intro hs
  have hr (n : ℕ) : 1≤linearRates n := by simp [linearRates]
  have hh := (actual_series_trace_iff linearRates hr (fun _ => (1 : ℝ)) t ht).mp (by simpa only [one_smul] using hs)
  apply SPDEWickModes.harmonic_not_summable
  change Summable (fun n : ℕ => 1/((n : ℝ)+1))
  simpa [linearRates] using hh

end OperatorDerivativeRewrite.Foundation.SPDEExponentialForcing

