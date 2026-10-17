import Foundation.GaussianTriadPhase
import Foundation.GaussianHermite

/-! Actual Hermite coefficients of the static Gaussian triad rate. -/
noncomputable section
open MeasureTheory Polynomial
namespace OperatorDerivativeRewrite.Foundation.GaussianTriadHermite
open GaussianCore GaussianTriadPhase
set_option backward.isDefEq.respectTransparency false

theorem polynomial_rate_integrable (p : ℝ[X]) :
    Integrable (fun c => p.eval c * phaseRate c) GaussianCore.γ := by
  have hm : MemLp (fun c => p.eval c * phaseRate c) 1 GaussianCore.γ :=
    mul_memLp (polynomial_memLp p 2 (by norm_num)) phaseRate_memLp
  exact hm.integrable (by norm_num)

theorem polynomial_rate_inner (p : ℝ[X]) :
    inner ℝ (polynomialL2 p) rateL2 =
      ∫ c, p.eval c * phaseRate c ∂GaussianCore.γ := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [polynomialL2_coeFn p, rateL2_coeFn] with c hp hr
  rw [hp, hr]
  simp only [Real.inner_apply]

theorem even_polynomial_orthogonal (p : ℝ[X])
    (hp : ∀ c : ℝ, p.eval (-c) = p.eval c) :
    inner ℝ (polynomialL2 p) rateL2 = 0 := by
  rw [polynomial_rate_inner]
  have he := gaussian_neg_preserving.integral_comp measurableEmbedding_neg
    (fun c => p.eval c * phaseRate c)
  simp only [hp, phaseRate_odd, mul_neg] at he
  rw [integral_neg] at he
  linarith

theorem hermite_eval_recurrence (n : ℕ) (c : ℝ) :
    (hermitePolynomial (n+2)).eval c =
      c * (hermitePolynomial (n+1)).eval c -
        (n+1 : ℝ) * (hermitePolynomial n).eval c := by
  rw [show n+2=(n+1)+1 by omega, hermitePolynomial_succ,
    divergencePolynomial, hermitePolynomial_derivative]
  simp

theorem hermite_eval_one (c : ℝ) : (hermitePolynomial 1).eval c = c := by
  simp [hermitePolynomial_succ, divergencePolynomial]

theorem hermite_eval_neg (n : ℕ) (c : ℝ) :
    (hermitePolynomial n).eval (-c) = (-1 : ℝ)^n * (hermitePolynomial n).eval c := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [hermite_eval_one]
  | more n hn hn1 =>
    rw [hermite_eval_recurrence, hermite_eval_recurrence, hn, hn1]
    simp only [pow_succ]
    ring

theorem hermite_even_eval (n : ℕ) (c : ℝ) :
    (hermitePolynomial (2*n)).eval (-c) = (hermitePolynomial (2*n)).eval c := by
  rw [hermite_eval_neg, pow_mul]
  norm_num

theorem even_coefficient_zero (n : ℕ) :
    hermiteBasis.repr rateL2 (2*n) = 0 := by
  rw [hermiteBasis_coefficient, normalizedHermite, real_inner_smul_left]
  change _ * inner ℝ (polynomialL2 (hermitePolynomial (2*n))) rateL2 = 0
  rw [even_polynomial_orthogonal _ (hermite_even_eval n), mul_zero]

theorem constant_coefficient_zero : hermiteBasis.repr rateL2 0 = 0 := by
  simpa using even_coefficient_zero 0

theorem first_coefficient_integral :
    hermiteBasis.repr rateL2 1 = ∫ c, phaseRate c*c ∂GaussianCore.γ := by
  rw [hermiteBasis_coefficient, normalizedHermite, real_inner_smul_left]
  change _ * inner ℝ (polynomialL2 (hermitePolynomial 1)) rateL2 = _
  rw [polynomial_rate_inner]
  simp only [Nat.factorial_one, Nat.cast_one, Real.sqrt_one, inv_one, one_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun c => by
    change (hermitePolynomial 1).eval c * phaseRate c = phaseRate c*c
    rw [hermite_eval_one, mul_comm])

theorem first_coefficient_negative : hermiteBasis.repr rateL2 1 < 0 := by
  rw [first_coefficient_integral]
  exact linear_correlation_negative

/-- The first nonzero Hermite index is exactly one, with rank explicitly defined. -/
theorem first_nonzero_index :
    hermiteBasis.repr rateL2 1 ≠ 0 ∧
      ∀ n : ℕ, n < 1 → hermiteBasis.repr rateL2 n = 0 := by
  refine ⟨ne_of_lt first_coefficient_negative, ?_⟩
  intro n hn
  have hn0 : n=0 := by omega
  subst n
  exact constant_coefficient_zero

theorem rate_hermite_expansion :
    HasSum (fun n => (inner ℝ (normalizedHermite n) rateL2) • normalizedHermite n)
      rateL2 := hermiteBasis_hasSum rateL2

end OperatorDerivativeRewrite.Foundation.GaussianTriadHermite
