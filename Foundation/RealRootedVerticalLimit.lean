import Foundation.RealRootedLaguerreLimit
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Vertical modulus monotonicity survives locally uniform limits of split
real polynomials. A nonzero entire limit therefore has only real zeros. -/
noncomputable section
open Polynomial Filter Set Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RealRootedVerticalLimit

theorem linear_factor_vertical_bound (x r a b : ℝ) (hab : a ^ 2 ≤ b ^ 2) :
    ‖((x : ℂ)+I*a)-r‖ ≤ ‖((x : ℂ)+I*b)-r‖ := by
  apply Real.sqrt_le_sqrt
  simpa [Complex.norm_def, Complex.normSq_apply, pow_two] using hab

theorem split_polynomial_vertical_bound (p : ℝ[X]) (hp : p.Splits)
    (x a b : ℝ) (hab : a ^ 2 ≤ b ^ 2) :
    ‖(p.map (algebraMap ℝ ℂ)).eval ((x : ℂ)+I*a)‖ ≤
      ‖(p.map (algebraMap ℝ ℂ)).eval ((x : ℂ)+I*b)‖ := by
  have hm (s : Multiset ℝ) :
      ‖((s.map (fun r => (X-C r : ℝ[X]))).prod.map (algebraMap ℝ ℂ)).eval
        ((x : ℂ)+I*a)‖ ≤
      ‖((s.map (fun r => (X-C r : ℝ[X]))).prod.map (algebraMap ℝ ℂ)).eval
        ((x : ℂ)+I*b)‖ := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons r s ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,Polynomial.map_mul,eval_mul,norm_mul]
      apply mul_le_mul _ ih (norm_nonneg _) (norm_nonneg _)
      simpa using linear_factor_vertical_bound x r a b hab
  rw [hp.eq_prod_roots]
  simpa only [Polynomial.map_mul,eval_mul,norm_mul,Polynomial.map_C,eval_C] using
    mul_le_mul_of_nonneg_left (hm p.roots)
      (norm_nonneg ((C p.leadingCoeff).map (algebraMap ℝ ℂ) |>.eval ((x : ℂ)+I*a)))

theorem limit_vertical_bound (P : ℕ → ℝ[X]) (f : ℂ → ℂ)
    (hP : ∀ n, (P n).Splits)
    (hlim : TendstoLocallyUniformlyOn
      (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) f atTop univ)
    (x a b : ℝ) (hab : a ^ 2 ≤ b ^ 2) :
    ‖f ((x : ℂ)+I*a)‖ ≤ ‖f ((x : ℂ)+I*b)‖ := by
  apply le_of_tendsto_of_tendsto
    ((hlim.tendsto_at (mem_univ _)).norm)
    ((hlim.tendsto_at (mem_univ _)).norm)
  exact Eventually.of_forall fun n => split_polynomial_vertical_bound (P n) (hP n) x a b hab

theorem real_zeros_of_vertical_bound (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hne : ∃ w, f w ≠ 0)
    (hvertical : ∀ x a b : ℝ, a ^ 2 ≤ b ^ 2 →
      ‖f ((x : ℂ)+I*a)‖ ≤ ‖f ((x : ℂ)+I*b)‖)
    (z : ℂ) (hz : f z = 0) : z.im = 0 := by
  by_contra hi
  let s : ℕ → ℂ := fun n => (z.re : ℂ)+I*Complex.ofReal (z.im/((n : ℝ)+1))
  have hs : Tendsto s atTop (𝓝 (z.re : ℂ)) := by
    have h : Tendsto (fun n : ℕ => z.im/((n : ℝ)+1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (show Tendsto (fun _ : ℕ => z.im) atTop (𝓝 z.im) from tendsto_const_nhds).mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
    simpa [s] using
      (show Tendsto (fun _ : ℕ => (z.re : ℂ)) atTop (𝓝 (z.re : ℂ)) from tendsto_const_nhds).add
        ((show Tendsto (fun _ : ℕ => I) atTop (𝓝 I) from tendsto_const_nhds).mul hc)
  have hm : ∀ n, s n ∈ {w : ℂ | f w = 0} \ {(z.re : ℂ)} := by
    intro n
    have hd : (1 : ℝ) ≤ (n : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hq : (z.im/((n : ℝ)+1))^2 ≤ z.im^2 := by
      rw [div_pow]
      exact div_le_self (sq_nonneg _) (by nlinarith)
    have he : (z.re : ℂ)+I*z.im = z := by
      apply Complex.ext <;> simp
    have hb := hvertical z.re (z.im/((n : ℝ)+1)) z.im hq
    rw [he,hz,norm_zero] at hb
    refine ⟨norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)),?_⟩
    intro hh
    have hh' : s n = (z.re : ℂ) := Set.mem_singleton_iff.mp hh
    have him := congrArg Complex.im hh'
    have hden : (n : ℝ)+1 ≠ 0 := by positivity
    have : z.im/((n : ℝ)+1) = 0 := by
      simpa only [s,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
        Complex.I_re,Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_add,add_zero] using him
    exact hi ((div_eq_zero_iff).mp this |>.resolve_right hden)
  have hclosure := mem_closure_of_tendsto hs (Eventually.of_forall hm)
  have ha : AnalyticOnNhd ℂ f univ := fun w _ => hf.analyticAt w
  have hzero := ha.eqOn_zero_of_preconnected_of_mem_closure
    isPreconnected_univ (mem_univ (z.re : ℂ)) hclosure
  obtain ⟨w,hw⟩ := hne
  exact hw (hzero (mem_univ w))

theorem real_zeros_of_locally_uniform_split_polynomials (P : ℕ → ℝ[X])
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hne : ∃ w, f w ≠ 0)
    (hP : ∀ n, (P n).Splits)
    (hlim : TendstoLocallyUniformlyOn
      (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) f atTop univ) :
    ∀ z : ℂ, f z = 0 → z.im = 0 :=
  real_zeros_of_vertical_bound f hf hne (limit_vertical_bound P f hP hlim)

end OperatorDerivativeRewrite.Foundation.RealRootedVerticalLimit
