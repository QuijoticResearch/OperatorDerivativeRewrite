import Foundation.GaussianExponentialMarkovPrediction
import Foundation.SPDEHilbertExponentialForcing
import Mathlib.Analysis.Normed.Group.Tannery

/-! Actual trace-admitted Hilbert-valued exponential responses are mean-square continuous. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.SPDEExponentialTimeContinuity
open InfiniteGaussian GaussianTimeHilbert SPDEExponentialForcing SPDEHilbertExponentialForcing
attribute [local instance] timeHilbert_secondCountable

def variance (rate t : ℝ≥0) : ℝ := (1-Real.exp (-2*(rate : ℝ)*(t : ℝ)))/(2*(rate : ℝ))

theorem response_inner (rate s t : ℝ≥0) :
    inner ℝ (responseVector rate t) (responseVector rate s)=
      Real.exp (-(rate : ℝ)*|(t : ℝ)-s|)*‖responseVector rate (min s t)‖^2 := by
  by_cases hst : s≤t
  · rw [min_eq_left hst,abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ)≤t from hst))]
    simpa only [GaussianExponentialMarkovPrediction.decay,real_inner_self_eq_norm_sq] using
      GaussianExponentialMarkovPrediction.response_pairing rate s s t le_rfl hst
  · have hts : t≤s := le_of_not_ge hst
    rw [min_eq_right hts,abs_of_nonpos (sub_nonpos.mpr (show (t : ℝ)≤s from hts))]
    have h := GaussianExponentialMarkovPrediction.response_pairing rate t t s le_rfl hts
    rw [real_inner_self_eq_norm_sq] at h
    have hc : inner ℝ (responseVector rate t) (responseVector rate s)=inner ℝ (responseVector rate s) (responseVector rate t) := real_inner_comm _ _
    rw [hc,h]
    congr 2
    simp only [GaussianExponentialMarkovPrediction.decay]
    ring

theorem response_distance_sq (rate : ℝ≥0) (hr : 0<rate) (s t : ℝ≥0) :
    ‖responseVector rate t-responseVector rate s‖^2=
      variance rate t+variance rate s-
        2*Real.exp (-(rate : ℝ)*|(t : ℝ)-s|)*variance rate (min s t) := by
  rw [norm_sub_sq_real,response_inner,responseVector_energy_exact rate t hr,
    responseVector_energy_exact rate s hr,responseVector_energy_exact rate (min s t) hr]
  unfold variance
  ring

theorem responseVector_continuous (rate : ℝ≥0) (hr : 0<rate) : Continuous (responseVector rate) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have hf : Continuous (fun t : ℝ≥0 => variance rate t+variance rate s-
      2*Real.exp (-(rate : ℝ)*|(t : ℝ)-s|)*variance rate (min s t)) := by
    unfold variance
    fun_prop
  have he : variance rate s+variance rate s-
      2*Real.exp (-(rate : ℝ)*|(s : ℝ)-s|)*variance rate (min s s)=0 := by simp; ring
  have ht : Tendsto (fun t => ‖responseVector rate t-responseVector rate s‖^2) (𝓝 s) (𝓝 0) := by
    simpa only [response_distance_sq rate hr,he] using hf.continuousAt.tendsto (x := s)
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hn

theorem response_increment_domination (rate : ℝ≥0) (hr : 0<rate) (s t : ℝ≥0) :
    ‖responseVector rate t-responseVector rate s‖^2≤2/(rate : ℝ) := by
  have hn := norm_sub_le (responseVector rate t) (responseVector rate s)
  have ht := responseVector_energy_upper rate t hr
  have hs := responseVector_energy_upper rate s hr
  have hb : ‖responseVector rate t-responseVector rate s‖^2≤
      2*(‖responseVector rate t‖^2+‖responseVector rate s‖^2) := by
    nlinarith [sq_nonneg (‖responseVector rate t‖-‖responseVector rate s‖),
      norm_nonneg (responseVector rate t-responseVector rate s),norm_nonneg (responseVector rate t),norm_nonneg (responseVector rate s)]
  have he : 2*(1/(2*(rate : ℝ))+1/(2*(rate : ℝ)))=2/(rate : ℝ) := by ring
  rw [← he]
  exact hb.trans (by linarith)

theorem profile_trace (rate : ℕ → ℝ≥0) (hrate : ∀ n,1≤rate n) (c : ℕ → ℝ)
    (hs : Summable (fun n => (c n)^2/(rate n : ℝ))) (t : ℝ≥0) :
    Summable (fun n => (c n)^2*‖responseVector (rate n) t‖^2) := by
  apply (hs.mul_left (1/2 : ℝ)).of_nonneg_of_le (fun n => by positivity)
  intro n
  have h := mul_le_mul_of_nonneg_left (responseVector_energy_upper (rate n) t (by linarith [hrate n])) (sq_nonneg (c n))
  convert h using 1 <;> ring

theorem increment_trace (rate : ℕ → ℝ≥0) (hrate : ∀ n,1≤rate n) (c : ℕ → ℝ)
    (hs : Summable (fun n => (c n)^2/(rate n : ℝ))) (s t : ℝ≥0) :
    Summable (fun n => (c n)^2*‖responseVector (rate n) t-responseVector (rate n) s‖^2) := by
  apply (hs.mul_left 2).of_nonneg_of_le (fun n => by positivity)
  intro n
  have h := mul_le_mul_of_nonneg_left
    (response_increment_domination (rate n) (by linarith [hrate n]) s t) (sq_nonneg (c n))
  convert h using 1 <;> ring

theorem field_sub (rate : ℕ → ℝ≥0) (hrate : ∀ n,1≤rate n) (c : ℕ → ℝ)
    (hs : Summable (fun n => (c n)^2/(rate n : ℝ))) (s t : ℝ≥0) :
    exponentialField rate c t-exponentialField rate c s=
      spatialResponse c (fun n => responseVector (rate n) t-responseVector (rate n) s) := by
  have ht := (spatialSeries_summable_iff c _).mpr (profile_trace rate hrate c hs t)
  have hh := (spatialSeries_summable_iff c _).mpr (profile_trace rate hrate c hs s)
  simpa only [exponentialField,spatialResponse,map_sub,smul_sub] using (ht.tsum_sub hh).symm

theorem field_increment_energy (rate : ℕ → ℝ≥0) (hrate : ∀ n,1≤rate n) (c : ℕ → ℝ)
    (hs : Summable (fun n => (c n)^2/(rate n : ℝ))) (s t : ℝ≥0) :
    ‖exponentialField rate c t-exponentialField rate c s‖^2=
      ∑' n,(c n)^2*‖responseVector (rate n) t-responseVector (rate n) s‖^2 := by
  rw [field_sub rate hrate c hs s t]
  exact (spatialResponse_energy _ _ (increment_trace rate hrate c hs s t)).tsum_eq.symm

theorem exponentialField_continuous (rate : ℕ → ℝ≥0) (hrate : ∀ n,1≤rate n) (c : ℕ → ℝ)
    (hs : Summable (fun n => (c n)^2/(rate n : ℝ))) : Continuous (exponentialField rate c) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have hn (n : ℕ) : Tendsto
      (fun t => (c n)^2*‖responseVector (rate n) t-responseVector (rate n) s‖^2) (𝓝 s) (𝓝 0) := by
    have h := (((responseVector_continuous (rate n) (by linarith [hrate n])).continuousAt.tendsto (x := s)).sub
      (tendsto_const_nhds (x := responseVector (rate n) s))).norm.pow 2
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero] using h.const_mul ((c n)^2)
  have ht := tendsto_tsum_of_dominated_convergence (hs.mul_left 2) hn
    (Eventually.of_forall (fun t n => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have h := mul_le_mul_of_nonneg_left
        (response_increment_domination (rate n) (by linarith [hrate n]) s t) (sq_nonneg (c n))
      convert h using 1 <;> ring))
  have ht' : Tendsto (fun t => ‖exponentialField rate c t-exponentialField rate c s‖^2) (𝓝 s) (𝓝 0) := by
    simpa only [field_increment_energy rate hrate c hs,tsum_zero] using ht
  have hlim := Real.continuous_sqrt.continuousAt.tendsto.comp ht'
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hlim

theorem quadraticField_continuous : Continuous quadraticField := by
  apply exponentialField_continuous quadraticRates quadraticRates_lower (fun _ => 1)
  simpa only [one_pow] using quadratic_trace_summable

theorem quadratic_divergence_continuous : Continuous
    (fun t => GaussianLinearFieldDivergenceCompletion.completedDivergence (quadraticField t)) :=
  GaussianLinearFieldDivergenceCompletion.completedDivergence.continuous.comp quadraticField_continuous

end OperatorDerivativeRewrite.Foundation.SPDEExponentialTimeContinuity


