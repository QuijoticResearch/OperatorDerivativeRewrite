import Foundation.HigherHeatL2
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! A concrete Gaussian Schwartz function, with all derivative decay proved. -/
noncomputable section
open MeasureTheory Filter Polynomial FourierTransform
open scoped SchwartzMap Topology ContDiff NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianSchwartzKernel

def gaussian (x : ℝ) : ℝ := Real.exp (-x^2)

theorem gaussian_hasDerivAt (x : ℝ) : HasDerivAt gaussian (-2*x*gaussian x) x := by
  unfold gaussian
  convert (((hasDerivAt_id x).pow 2).neg.exp) using 1 <;> simp <;> ring

theorem gaussian_smooth : ContDiff ℝ ∞ gaussian := by unfold gaussian; fun_prop

theorem weighted_bound (k : ℕ) : ∃ C : ℝ, ∀ x : ℝ, |x|^k * gaussian x ≤ C := by
  have ht : Tendsto (fun x : ℝ => |x|^k * gaussian x) (cocompact ℝ) (𝓝 0) := by
    simpa [gaussian,Real.rpow_natCast] using
      tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (by norm_num : (0 : ℝ) < 1) (k : ℝ)
  have hc : Continuous (fun x : ℝ => |x|^k * gaussian x) := by
    unfold gaussian
    fun_prop
  obtain ⟨C,hC⟩ := (hc.isBounded_range_iff_isBigO.mpr (ht.isBigO_one ℝ)).bddAbove
  exact ⟨C,fun x => hC (Set.mem_range_self x)⟩

theorem polynomial_weighted_bound (P : Polynomial ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x|^k * |P.eval x * gaussian x| ≤ C := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨A,hA⟩ := hP
    obtain ⟨B,hB⟩ := hQ
    refine ⟨A+B,fun x => ?_⟩
    simp only [eval_add,add_mul]
    calc
      |x|^k * |P.eval x * gaussian x + Q.eval x * gaussian x| ≤
          |x|^k * (|P.eval x * gaussian x| + |Q.eval x * gaussian x|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
      _ ≤ A+B := by rw [mul_add]; exact add_le_add (hA x) (hB x)
  | monomial n c =>
    obtain ⟨C,hC⟩ := weighted_bound (k+n)
    refine ⟨|c| * C,fun x => ?_⟩
    have hg : 0 < gaussian x := Real.exp_pos _
    simp only [eval_monomial,abs_mul,abs_pow,abs_of_pos hg]
    calc
      |x|^k * (|c| * |x|^n * gaussian x) = |c| * (|x|^(k+n) * gaussian x) := by rw [pow_add]; ring
      _ ≤ |c| * C := mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

theorem iteratedDeriv_polynomial (n : ℕ) :
    ∃ P : Polynomial ℝ, iteratedDeriv n gaussian = fun x => P.eval x * gaussian x := by
  induction n with
  | zero => exact ⟨1,by funext x; simp⟩
  | succ n hn =>
    obtain ⟨P,hP⟩ := hn
    refine ⟨P.derivative - C 2 * X * P, ?_⟩
    rw [iteratedDeriv_succ,hP]
    funext x
    rw [show deriv (fun x => P.eval x * gaussian x) x =
      P.derivative.eval x * gaussian x + P.eval x * (-2*x*gaussian x) from
      ((P.hasDerivAt x).mul (gaussian_hasDerivAt x)).deriv]
    simp only [eval_sub,eval_mul,eval_C,eval_X]
    ring

def realSchwartz : 𝓢(ℝ,ℝ) where
  toFun := gaussian
  smooth' := gaussian_smooth
  decay' := by
    intro k n
    obtain ⟨P,hP⟩ := iteratedDeriv_polynomial n
    obtain ⟨C,hC⟩ := polynomial_weighted_bound P k
    refine ⟨C,fun x => ?_⟩
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,hP,Real.norm_eq_abs] using hC x

def complexSchwartz : 𝓢(ℝ,ℂ) := realSchwartz.postcompCLM Complex.ofRealCLM

theorem complexSchwartz_apply (x : ℝ) : complexSchwartz x = (gaussian x : ℂ) := rfl

theorem power_proper (m : ℕ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) :
    ∃ (k : ℕ) (C : ℝ), ∀ x : ℝ, ‖x‖ ≤ C * (1 + ‖a*x^m‖)^k := by
  refine ⟨1,1+1/a,fun x => ?_⟩
  have hp : |x| ≤ 1+|x|^m := by
    by_cases h : |x| ≤ 1
    · exact h.trans (by linarith [pow_nonneg (abs_nonneg x) m])
    · exact (le_self_pow₀ (le_of_not_ge h) hm.ne').trans (by linarith)
  simp only [pow_one,Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos ha]
  calc
    |x| ≤ 1+|x|^m := hp
    _ ≤ 1+|x|^m + a*|x|^m + 1/a := by
      have h1 : 0 ≤ a*|x|^m := by positivity
      have h2 : 0 ≤ 1/a := by positivity
      linarith
    _ = (1+1/a)*(1+a*|x|^m) := by field_simp; ring

def evenSymbol (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLM ℝ (g := fun x : ℝ => (Real.sqrt t*(2*Real.pi)^m)*x^m)
    (by fun_prop)
    (power_proper m hm _ (mul_pos (Real.sqrt_pos.2 ht) (pow_pos (by positivity) _)))
    complexSchwartz

theorem evenSymbol_apply (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (x : ℝ) :
    evenSymbol m hm t ht x = HigherHeatL2.symbol m t x := by
  change (Real.exp (-((Real.sqrt t*(2*Real.pi)^m)*x^m)^2) : ℂ) =
    (Real.exp (-(t : ℝ)*(2*Real.pi*x)^(2*m)) : ℂ)
  congr 2
  simp only [show 2*m=m*2 by omega,pow_mul,mul_pow,Real.sq_sqrt t.coe_nonneg]
  ring

def evenKernel (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) : 𝓢(ℝ,ℂ) :=
  𝓕⁻ (evenSymbol m hm t ht)

theorem evenKernel_fourier (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    𝓕 (evenKernel m hm t ht) = evenSymbol m hm t ht := fourier_fourierInv_eq _

theorem evenKernel_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    Integrable (evenKernel m hm t ht) := (evenKernel m hm t ht).integrable

theorem evenKernel_convolution (m : ℕ) (hm : 0 < m) (s t : ℝ≥0)
    (hs : 0 < s) (ht : 0 < t) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (evenKernel m hm s hs) (evenKernel m hm t ht) =
      evenKernel m hm (s+t) (add_pos hs ht) := by
  apply (fourierEquiv ℂ 𝓢(ℝ,ℂ)).injective
  change 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (evenKernel m hm s hs) (evenKernel m hm t ht)) =
    𝓕 (evenKernel m hm (s+t) (add_pos hs ht))
  rw [SchwartzMap.fourier_convolution,evenKernel_fourier,evenKernel_fourier,evenKernel_fourier]
  ext x
  simp only [SchwartzMap.pairing_apply_apply,ContinuousLinearMap.mul_apply',evenSymbol_apply]
  exact (HigherHeatL2.symbol_add m s t x).symm

theorem evenKernel_normalization (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    ∫ x, evenKernel m hm t ht x = 1 := by
  have h := congrArg (fun f : 𝓢(ℝ,ℂ) => f 0) (evenKernel_fourier m hm t ht)
  rw [SchwartzMap.fourier_coe,evenSymbol_apply] at h
  simpa [Real.fourier_eq,HigherHeatL2.symbol,hm.ne'] using h

theorem evenSymbol_neg (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (x : ℝ) :
    evenSymbol m hm t ht (-x) = evenSymbol m hm t ht x := by
  simp only [evenSymbol_apply,HigherHeatL2.symbol]
  congr 2
  rw [show 2*Real.pi*(-x)=-(2*Real.pi*x) by ring,neg_pow,Even.neg_pow (even_two_mul m)]
  simp

theorem evenKernel_conj (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (x : ℝ) :
    starRingEnd ℂ (evenKernel m hm t ht x) = evenKernel m hm t ht x := by
  simp only [evenKernel,SchwartzMap.fourierInv_coe,Real.fourierInv_eq',real_inner_comm,
    RCLike.inner_apply,conj_trivial]
  rw [← integral_conj]
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [smul_eq_mul,map_mul,evenSymbol_neg,evenSymbol_apply,
      HigherHeatL2.symbol,Complex.conj_ofReal]
    rw [← Complex.exp_conj]
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      exact map_ofNat (starRingEnd ℂ) 2
    congr 1 <;> norm_num [mul_neg,Even.neg_pow (even_two_mul m),htwo]

end OperatorDerivativeRewrite.Foundation.GaussianSchwartzKernel
