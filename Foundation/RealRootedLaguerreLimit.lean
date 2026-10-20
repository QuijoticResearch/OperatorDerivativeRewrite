import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! The Laguerre inequality for split real polynomials and their locally
uniform complex limits. Repeated roots and zeros at the evaluation point
are included; the proof never divides by the polynomial value. -/
noncomputable section
open Polynomial Filter Set Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RealRootedLaguerreLimit

theorem product_laguerre_identity (p q : ℝ[X]) (x : ℝ) :
    (p*q).derivative.eval x ^ 2 -
        (p*q).eval x * (p*q).derivative.derivative.eval x =
      q.eval x ^ 2 * (p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x) +
      p.eval x ^ 2 * (q.derivative.eval x ^ 2 - q.eval x * q.derivative.derivative.eval x) := by
  simp only [derivative_mul, derivative_add, eval_add, eval_mul]
  ring

theorem split_polynomial_laguerre_nonneg (p : ℝ[X]) (hp : p.Splits) (x : ℝ) :
    0 ≤ p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x := by
  have hm : ∀ s : Multiset ℝ,
      0 ≤ (s.map (fun r => (X - C r : ℝ[X]))).prod.derivative.eval x ^ 2 -
        (s.map (fun r => (X - C r : ℝ[X]))).prod.eval x *
          (s.map (fun r => (X - C r : ℝ[X]))).prod.derivative.derivative.eval x := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons r s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [product_laguerre_identity]
      have hl : 0 ≤ (X - C r : ℝ[X]).derivative.eval x ^ 2 -
          (X - C r : ℝ[X]).eval x * (X - C r : ℝ[X]).derivative.derivative.eval x := by
        simp
      exact add_nonneg (mul_nonneg (sq_nonneg _) hl) (mul_nonneg (sq_nonneg _) ih)
  rw [hp.eq_prod_roots, product_laguerre_identity]
  simpa using mul_nonneg (sq_nonneg p.leadingCoeff) (hm p.roots)

theorem map_eval_real (p : ℝ[X]) (x : ℝ) :
    (p.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
  simpa using (Polynomial.eval_map_apply (p := p) (algebraMap ℝ ℂ) x)

theorem mapped_deriv (p : ℝ[X]) :
    deriv (fun z : ℂ => (p.map (algebraMap ℝ ℂ)).eval z) =
      fun z => (p.derivative.map (algebraMap ℝ ℂ)).eval z := by
  funext z
  simp only [Polynomial.deriv, derivative_map]

theorem laguerre_nonneg_of_locally_uniform_split_polynomials_on
    (P : ℕ → ℝ[X]) (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hP : ∀ n, (P n).Splits)
    (hlim : TendstoLocallyUniformlyOn
      (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) f atTop U)
    (x : ℝ) (hx : (x : ℂ) ∈ U) :
    0 ≤ (deriv f (x : ℂ)).re ^ 2 -
      (f (x : ℂ)).re * (deriv (deriv f) (x : ℂ)).re := by
  have hhol : ∀ᶠ n : ℕ in atTop,
      DifferentiableOn ℂ (fun z => ((P n).map (algebraMap ℝ ℂ)).eval z) U :=
    Eventually.of_forall fun n => Polynomial.differentiableOn _
  have hlim1 := hlim.deriv hhol hU
  have hhol1 : ∀ᶠ n : ℕ in atTop,
      DifferentiableOn ℂ
        (deriv (fun z => ((P n).map (algebraMap ℝ ℂ)).eval z)) U := by
    filter_upwards [] with n
    rw [mapped_deriv]
    exact Polynomial.differentiableOn _
  have hlim2 := hlim1.deriv hhol1 hU
  have h0 := Complex.continuous_re.continuousAt.tendsto.comp (hlim.tendsto_at hx)
  have h1 := Complex.continuous_re.continuousAt.tendsto.comp (hlim1.tendsto_at hx)
  have h2 := Complex.continuous_re.continuousAt.tendsto.comp (hlim2.tendsto_at hx)
  have hconv := (h1.pow 2).sub (h0.mul h2)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hconv
  filter_upwards [] with n
  simpa only [Function.comp_apply, mapped_deriv, map_eval_real, Complex.ofReal_re]
    using split_polynomial_laguerre_nonneg (P n) (hP n) x

end OperatorDerivativeRewrite.Foundation.RealRootedLaguerreLimit
