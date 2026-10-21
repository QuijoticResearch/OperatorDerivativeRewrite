import Foundation.MultivariateFactorialSubstitution
import Mathlib.Data.Nat.Choose.Sum

/-! Finite binomial product rule for every iterate of the verified polynomial
 directional derivative. Reuses Mathlib's Pascal sum identity. -/
noncomputable section
open scoped BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatIteratedLeibniz
open MultivariateFactorialDomain

theorem derivative_iterate_mul {ι : Type*} (v : ι → ℝ) (F G : MvPolynomial ι ℝ) (r : ℕ) :
    (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r] (F*G) =
      ∑ k ∈ Finset.range (r+1), r.choose k •
        ((polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[k] F *
          (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r-k] G) := by
  let D := polynomialDerivative v
  change (D : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r] (F*G) =
    ∑ k ∈ Finset.range (r+1), r.choose k •
      ((D : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[k] F *
        (D : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r-k] G)
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    calc
      _ = (∑ k ∈ Finset.range (r+1), r.choose k •
          ((D : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[k] F *
            (D : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r+1-k] G)) +
        ∑ k ∈ Finset.range (r+1), r.choose k •
          ((D : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[k+1] F *
            (D : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r-k] G) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have he : r-k+1=r+1-k := by have := Finset.mem_range.mp hk; omega
        simp only [map_nsmul, Derivation.leibniz, smul_eq_mul,
          ← Function.iterate_succ_apply', nsmul_add]
        rw [mul_comm ((D : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r-k] G)
          ((D : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[k+1] F)]
        simp only [Nat.succ_eq_add_one, he]
      _ = _ := (Finset.sum_choose_succ_nsmul
        (fun a b => (D : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[a] F *
          (D : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[b] G) r).symm

end OperatorDerivativeRewrite.Foundation.HigherHeatIteratedLeibniz
