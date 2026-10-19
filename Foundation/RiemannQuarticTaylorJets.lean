import Foundation.RiemannQuarticRealCertificate
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual normalized derivatives underlying the interval Taylor prototype.
These identities do not certify any numerical derivative enclosure. -/
noncomputable section
open MeasureTheory
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticTaylorJets
open RiemannQuarticRealCertificate RiemannThetaTruncation RiemannQuarticKernel

def coefficient (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv n f x/(n.factorial : ℝ)

theorem coefficient_zero (f : ℝ → ℝ) (x : ℝ) : coefficient f 0 x=f x := by
  simp [coefficient]

theorem coefficient_mul (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x : ℝ) :
    coefficient (fun u => f u*g u) n x =
      ∑ i ∈ Finset.range (n+1), coefficient f i x*coefficient g (n-i) x := by
  simp only [coefficient]
  rw [iteratedDeriv_fun_mul (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
  have hfac : (n.choose i : ℝ)*(i.factorial : ℝ)*((n-i).factorial : ℝ) =
      (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hi0 : (i.factorial : ℝ) ≠ 0 := by positivity
  have hni : ((n-i).factorial : ℝ) ≠ 0 := by positivity
  rw [div_mul_div_comm]
  apply (div_eq_div_iff hn (mul_ne_zero hi0 hni)).mpr
  rw [← hfac]
  ring

theorem coefficient_deriv (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    coefficient (deriv f) n x = (n+1 : ℝ)*coefficient f (n+1) x := by
  simp only [coefficient, ← iteratedDeriv_succ', Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem coefficient_exp_succ (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) :
    coefficient (fun u => Real.exp (f u)) (n+1) x =
      (∑ i ∈ Finset.range (n+1),
        (i+1 : ℝ)*coefficient f (i+1) x*
          coefficient (fun u => Real.exp (f u)) (n-i) x)/(n+1 : ℝ) := by
  have hd : deriv (fun u => Real.exp (f u)) =
      fun u => deriv f u*Real.exp (f u) := by
    funext u
    rw [((hf.differentiable (by simp)).differentiableAt.hasDerivAt.exp).deriv]
    ring
  have h := coefficient_deriv (fun u => Real.exp (f u)) n x
  rw [hd, coefficient_mul (deriv f) (fun u => Real.exp (f u))
    (contDiff_infty_iff_deriv.mp hf).2
    (Real.contDiff_exp.comp hf)] at h
  simp_rw [coefficient_deriv] at h
  apply (eq_div_iff (by positivity : (n+1 : ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using h.symm

theorem partialKernel_contDiff (N : ℕ) : ContDiff ℝ ∞ (partialKernel N) := by
  unfold partialKernel thetaPrefix thetaTerm
  fun_prop

theorem channel_contDiff (k : ℕ) (x : ℝ) : ContDiff ℝ ∞ (channel k x) := by
  unfold channel
  split <;> fun_prop

theorem realIntegrand_contDiff (N k : ℕ) (x : ℝ) :
    ContDiff ℝ ∞ (realIntegrand N k x) := by
  have hp := partialKernel_contDiff N
  have hc := channel_contDiff k x
  unfold realIntegrand
  fun_prop

def localPolynomial (f : ℝ → ℝ) (n : ℕ) (c u : ℝ) : ℝ :=
  taylorWithinEval f n Set.univ c u

theorem localPolynomial_eq_sum (f : ℝ → ℝ) (n : ℕ) (c u : ℝ) :
    localPolynomial f n c u =
      ∑ i ∈ Finset.range (n+1), coefficient f i c*(u-c)^i := by
  simp only [localPolynomial, taylor_within_apply, iteratedDerivWithin_univ,
    smul_eq_mul, coefficient, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem localPolynomial_integral (f : ℝ → ℝ) (n : ℕ) (c h : ℝ) :
    (∫ u in c-h..c+h, localPolynomial f n c u) =
      ∑ i ∈ Finset.range (n+1),
        coefficient f i c*(h^(i+1)-(-h)^(i+1))/(i+1 : ℝ) := by
  simp_rw [localPolynomial_eq_sum]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (f := fun u : ℝ => u^i) c,
      integral_pow]
    ring
  · intro i hi
    exact (by fun_prop : Continuous (fun u : ℝ => coefficient f i c*(u-c)^i)).intervalIntegrable
      (μ := volume) (a := c-h) (b := c+h)

theorem local_error (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (c h M : ℝ) (hh : 0 < h) (hM : 0 ≤ M)
    (hbound : ∀ v ∈ Set.Icc (c-h) (c+h), |coefficient f (n+1) v| ≤ M)
    (u : ℝ) (hu : u ∈ Set.Icc (c-h) (c+h)) :
    |f u-localPolynomial f n c u| ≤ M*h^(n+1) := by
  by_cases hcu : c=u
  · subst u
    simp only [localPolynomial, taylorWithinEval_self, sub_self, abs_zero]
    positivity
  obtain ⟨v, hv, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hcu
    ((hf.of_le (by simp)).contDiffOn : ContDiffOn ℝ (n+1) f (Set.uIcc c u))
  have hc : c ∈ Set.uIcc c u := by simp
  have hp : taylorWithinEval f n (Set.uIcc c u) c u=localPolynomial f n c u := by
    simp only [localPolynomial, taylor_within_apply, iteratedDerivWithin_univ]
    apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hcu)
      (hf.of_le (by simp)).contDiffAt hc]
  rw [hp] at he
  have hv' : v ∈ Set.Icc (c-h) (c+h) := by
    change min c u < v ∧ v < max c u at hv
    rcases le_total c u with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at hv
      constructor <;> linarith [hu.1, hu.2]
    · rw [min_eq_right hle, max_eq_left hle] at hv
      constructor <;> linarith [hu.1, hu.2]
  have hd : |u-c| ≤ h := abs_le.mpr (by constructor <;> linarith [hu.1, hu.2])
  have he' : f u-localPolynomial f n c u=coefficient f (n+1) v*(u-c)^(n+1) := by
    rw [he]
    unfold coefficient
    ring
  rw [he', abs_mul, abs_pow]
  exact mul_le_mul (hbound v hv') (pow_le_pow_left₀ (abs_nonneg _) hd _)
    (pow_nonneg (abs_nonneg _) _) hM

theorem local_integral_error (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (c h M : ℝ) (hh : 0 < h) (hM : 0 ≤ M)
    (hbound : ∀ v ∈ Set.Icc (c-h) (c+h), |coefficient f (n+1) v| ≤ M) :
    |(∫ u in c-h..c+h, f u)-(∫ u in c-h..c+h, localPolynomial f n c u)| ≤
      (M*h^(n+1))*(2*h) := by
  have hp : Continuous (localPolynomial f n c) := by
    have hs : localPolynomial f n c = fun u =>
        ∑ i ∈ Finset.range (n+1), coefficient f i c*(u-c)^i := by
      funext u
      exact localPolynomial_eq_sum f n c u
    rw [hs]
    fun_prop
  rw [← intervalIntegral.integral_sub
    (hf.continuous.intervalIntegrable (μ := volume) (a := c-h) (b := c+h))
    (hp.intervalIntegrable (μ := volume) (a := c-h) (b := c+h))]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := c-h) (b := c+h) (C := M*h^(n+1))
    (f := fun u => f u-localPolynomial f n c u) (by
      intro u hu
      rw [Set.uIoc_of_le (by linarith : c-h ≤ c+h)] at hu
      exact local_error f hf n c h M hh hM hbound u ⟨hu.1.le, hu.2⟩)
  have hab : |c+h-(c-h)|=2*h := by rw [abs_of_pos (by linarith)]; ring
  simpa only [Real.norm_eq_abs, hab] using he

end OperatorDerivativeRewrite.Foundation.RiemannQuarticTaylorJets
