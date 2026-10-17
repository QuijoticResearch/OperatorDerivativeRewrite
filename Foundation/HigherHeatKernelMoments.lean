import Foundation.HigherHeatSignedLaws
import Mathlib.Analysis.Complex.RealDeriv

/-! Second moments of the actual higher-order heat kernels. -/
noncomputable section
open MeasureTheory FourierTransform Polynomial
open scoped NNReal SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatKernelMoments
open GaussianSchwartzKernel HigherHeatSignedLaws

theorem exponential_second_zero (n : ℕ) (hn : 3 ≤ n) (a : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => (Real.exp (-a*x^n) : ℂ)) 0 = 0 := by
  let f : ℝ → ℝ := fun x => Real.exp (-a*x^n)
  let g : ℝ → ℝ := fun x => Real.exp (-a*x^n) * (-a*(n : ℝ)*x^(n-1))
  have hd (x : ℝ) : HasDerivAt f (g x) x := by
    convert (((hasDerivAt_id x).pow n).const_mul (-a)).exp using 1 <;> simp [f,g] <;> ring
  have hg : HasDerivAt g 0 0 := by
    convert (hd 0).mul (((hasDerivAt_id (0 : ℝ)).pow (n-1)).const_mul (-a*(n : ℝ))) using 1
    · rfl
    · simp [g,show n ≠ 0 by omega,show n-1 ≠ 0 by omega,show n-1-1 ≠ 0 by omega]
  have hdf : deriv (fun x : ℝ => (f x : ℂ)) = fun x => (g x : ℂ) := by
    funext x
    exact (hd x).ofReal_comp.deriv
  change iteratedDeriv 2 (fun x : ℝ => (f x : ℂ)) 0 = 0
  rw [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ,
    show (1 : ℕ)=0+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero]
  rw [hdf]
  exact hg.ofReal_comp.deriv

theorem symbol_second_zero (m : ℕ) (hm : 2 ≤ m) (t : ℝ≥0) :
    iteratedDeriv 2 (HigherHeatL2.symbol m t) 0 = 0 := by
  have he : HigherHeatL2.symbol m t =
      fun x : ℝ => (Real.exp (-((t : ℝ)*(2*Real.pi)^(2*m))*x^(2*m)) : ℂ) := by
    funext x
    simp only [HigherHeatL2.symbol,mul_pow]
    congr 2
    ring
  rw [he]
  exact exponential_second_zero (2*m) (by omega) ((t : ℝ)*(2*Real.pi)^(2*m))

theorem complex_second_moment (m : ℕ) (hm : 2 ≤ m) (t : ℝ≥0) (ht : 0 < t) :
    ∫ x : ℝ, (x : ℂ)^2 * evenKernel m (by omega) t ht x = 0 := by
  let K := evenKernel m (by omega : 0 < m) t ht
  have hI (n : ℕ) : Integrable (fun x : ℝ => x^n • K x) := by
    have h : (fun x : ℝ => x^n).HasTemperateGrowth := by fun_prop
    simpa only [SchwartzMap.smulLeftCLM_apply h] using
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x^n) K).integrable
  have hf := Real.iteratedDeriv_fourier (N := ⊤) (fun n _ => hI n) (n := 2) (by simp)
  have hF : 𝓕 (K : ℝ → ℂ) = HigherHeatL2.symbol m t := by
    funext x
    rw [← SchwartzMap.fourier_coe,evenKernel_fourier,evenSymbol_apply]
  rw [hF] at hf
  have hz := congrFun hf 0
  rw [symbol_second_zero m hm t] at hz
  simp only [Real.fourier_eq,inner_zero_right,neg_zero,AddChar.map_zero_eq_one,one_smul] at hz
  have he : (∫ x : ℝ, (-2*Real.pi*Complex.I*(x : ℂ))^2 • K x) =
      (-(2*Real.pi)^2 : ℂ) * ∫ x : ℝ, (x : ℂ)^2 * K x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [smul_eq_mul]
      ring_nf
      simp
  rw [he] at hz
  have hc : (-(2*Real.pi)^2 : ℂ) ≠ 0 := by exact neg_ne_zero.mpr (pow_ne_zero 2 (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)))
  exact (mul_eq_zero.mp hz.symm).resolve_left hc

theorem real_second_moment_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    Integrable (fun x : ℝ => x^2 * realKernel m hm t ht x) := by
  have hg : (fun x : ℝ => x^2).HasTemperateGrowth := by fun_prop
  convert (SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x^2)
    (realKernel m hm t ht)).integrable (μ := volume) using 1
  funext x
  simp only [SchwartzMap.smulLeftCLM_apply hg,smul_eq_mul]

theorem real_second_moment (m : ℕ) (hm : 2 ≤ m) (t : ℝ≥0) (ht : 0 < t) :
    ∫ x : ℝ, x^2 * realKernel m (by omega) t ht x = 0 := by
  have h := complex_second_moment m hm t ht
  simp_rw [← realKernel_coe m (by omega) t ht] at h
  have he : (∫ x : ℝ, (x : ℂ)^2 * (realKernel m (by omega) t ht x : ℂ)) =
      ((∫ x : ℝ, x^2 * realKernel m (by omega) t ht x : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_pow,← Complex.ofReal_mul]
    exact integral_complex_ofReal
  rw [he] at h
  exact_mod_cast h

theorem not_nonnegative_ae (m : ℕ) (hm : 2 ≤ m) (t : ℝ≥0) (ht : 0 < t) :
    ¬ ∀ᵐ x : ℝ ∂volume, 0 ≤ realKernel m (by omega) t ht x := by
  intro hpos
  let K := realKernel m (by omega : 0 < m) t ht
  have hi : Integrable (fun x : ℝ => x^2*K x) := real_second_moment_integrable m (by omega) t ht
  have h0 : (fun x : ℝ => x^2*K x) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (hpos.mono fun x hx => mul_nonneg (sq_nonneg x) hx) hi).mp (real_second_moment m hm t ht)
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp only [not_not,Set.ofPred_eq_eq_singleton]
    exact measure_singleton 0
  have hk : K =ᵐ[volume] 0 := by
    filter_upwards [h0,hne] with x hx hn
    exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero 2 hn)
  have hz : ∫ x, K x = 0 := by
    rw [integral_congr_ae hk]
    simp only [Pi.zero_apply,integral_zero]
  have ho : ∫ x, K x = 1 := realKernel_integral m (by omega) t ht
  linarith

theorem exists_negative (m : ℕ) (hm : 2 ≤ m) (t : ℝ≥0) (ht : 0 < t) :
    ∃ x : ℝ, realKernel m (by omega) t ht x < 0 := by
  by_contra h
  push Not at h
  exact not_nonnegative_ae m hm t ht (Filter.Eventually.of_forall h)

theorem norm_integral_gt_one (m : ℕ) (hm : 2 ≤ m) (t : ℝ≥0) (ht : 0 < t) :
    1 < ∫ x : ℝ, ‖realKernel m (by omega) t ht x‖ := by
  by_contra hn
  have hb : (∫ x : ℝ, ‖realKernel m (by omega) t ht x‖) ≤ 1 := le_of_not_gt hn
  let K := realKernel m (by omega : 0 < m) t ht
  have hi : Integrable (fun x : ℝ => ‖K x‖-K x) := K.integrable.norm.sub K.integrable
  have hp : ∀ᵐ x : ℝ ∂volume, 0 ≤ ‖K x‖-K x :=
    Filter.Eventually.of_forall fun x => sub_nonneg.mpr (by simpa only [Real.norm_eq_abs] using le_abs_self (K x))
  have hz : ∫ x : ℝ, ‖K x‖-K x = 0 := by
    have hnon := integral_nonneg_of_ae hp
    rw [integral_sub K.integrable.norm K.integrable] at hnon ⊢
    have hmass : ∫ x, K x = 1 := realKernel_integral m (by omega) t ht
    rw [hmass] at hnon ⊢
    exact le_antisymm (sub_nonpos.mpr hb) hnon
  have he := (integral_eq_zero_iff_of_nonneg_ae hp hi).mp hz
  apply not_nonnegative_ae m hm t ht
  filter_upwards [he] with x hx
  change 0 ≤ K x
  have hn := norm_nonneg (K x)
  change ‖K x‖-K x=0 at hx
  linarith

end OperatorDerivativeRewrite.Foundation.HigherHeatKernelMoments
