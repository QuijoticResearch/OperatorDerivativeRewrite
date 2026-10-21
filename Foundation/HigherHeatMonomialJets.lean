import Foundation.HigherHeatIteratedLeibniz
import Mathlib.Data.Nat.Factorial.Basic

/-! Exact finite jets of powers in the existing polynomial derivative calculus. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.HigherHeatMonomialJets
open MultivariateFactorialDomain

theorem derivative_mul_power {ι : Type*} (v : ι → ℝ) (F A : MvPolynomial ι ℝ)
    (hF : polynomialDerivative v F = 0) (hA : polynomialDerivative v A = 1) (r : ℕ) :
    polynomialDerivative v (F*A^r) = r • (F*A^(r-1)) := by
  rw [Derivation.leibniz, hF, Derivation.leibniz_pow, hA]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

theorem derivative_iterate_mul_power {ι : Type*} (v : ι → ℝ) (F A : MvPolynomial ι ℝ)
    (hF : polynomialDerivative v F = 0) (hA : polynomialDerivative v A = 1) (r k : ℕ) :
    (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[k] (F*A^r) =
      r.descFactorial k • (F*A^(r-k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_nsmul, derivative_mul_power v F A hF hA,
      Nat.descFactorial_succ]
    simp only [smul_smul, Nat.sub_sub, Nat.mul_comm]

end OperatorDerivativeRewrite.Foundation.HigherHeatMonomialJets
