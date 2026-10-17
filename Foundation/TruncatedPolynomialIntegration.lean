import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Finite moment integrability and matching imply actual polynomial integral matching. -/
noncomputable section
open MeasureTheory Polynomial
namespace OperatorDerivativeRewrite.Foundation.TruncatedPolynomialIntegration
set_option backward.isDefEq.respectTransparency false

theorem polynomial_integral_match (μ : Measure ℝ) (E : Polynomial ℝ →ₗ[ℝ] ℝ) (d : ℕ)
    (hi : ∀ n ≤ d, Integrable (fun x : ℝ => x^n) μ)
    (hm : ∀ n ≤ d, (∫ x : ℝ, x^n ∂μ) = E (X^n))
    (g : Polynomial ℝ) (hg : g.natDegree ≤ d) :
    Integrable (fun x => g.eval x) μ ∧ (∫ x, g.eval x ∂μ) = E g := by
  have hp := g.as_sum_range_C_mul_X_pow' (show g.natDegree < d+1 by omega)
  have hf : (fun x => g.eval x) =
      fun x => ∑ n ∈ Finset.range (d+1), g.coeff n*x^n := by
    funext x
    conv_lhs => rw [hp]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  have hint : ∀ n ∈ Finset.range (d+1),
      Integrable (fun x : ℝ => g.coeff n*x^n) μ := by
    intro n hn
    exact (hi n (by have := Finset.mem_range.mp hn; omega)).const_mul _
  refine ⟨?_, ?_⟩
  · exact (integrable_finsetSum _ hint).congr
      (Filter.Eventually.of_forall fun x => (congrFun hf x).symm)
  · calc
      (∫ x, g.eval x ∂μ) =
          ∫ x, ∑ n ∈ Finset.range (d+1), g.coeff n*x^n ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => congrFun hf x)
      _ = ∑ n ∈ Finset.range (d+1), g.coeff n*(∫ x : ℝ, x^n ∂μ) := by
        rw [integral_finsetSum _ hint]
        simp only [integral_const_mul]
      _ = E g := by
        conv_rhs => rw [hp]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [hm n (by have := Finset.mem_range.mp hn; omega), ← smul_eq_C_mul, map_smul]
        rfl

end OperatorDerivativeRewrite.Foundation.TruncatedPolynomialIntegration
