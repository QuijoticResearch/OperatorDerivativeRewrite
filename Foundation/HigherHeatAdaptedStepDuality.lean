import Foundation.MultivariateConditionalStein
import Foundation.MultivariateFactorialSubstitution

/-! Finite signed stochastic step sums and their adapted derivative duality.
All expectations below are integrals against the actual signed increment law.
Adaptation is a polynomial variable condition, not a probabilistic assumption. -/
noncomputable section
open scoped BigOperators NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAdaptedStepDuality
open MultivariateFactorialDomain MultivariateFactorialSubstitution
open MultivariateConditionalStein HigherHeatMultivariateMoments

variable {ι : Type*} [DecidableEq ι]

theorem derivative_zero_of_missing (j : ι) (F : MvPolynomial ι ℝ)
    (hF : j ∉ F.vars) : polynomialDerivative (Pi.single j 1) F = 0 := by
  apply MvPolynomial.derivation_eq_zero_of_forall_mem_vars
  intro i hi
  rw [polynomialDerivative_X]
  have hij : i ≠ j := by intro he; subst i; exact hF hi
  simp [hij]

omit [DecidableEq ι] in
theorem iterate_mul_of_derivative_zero (v : ι → ℝ) (F G : MvPolynomial ι ℝ)
    (hF : polynomialDerivative v F = 0) (r : ℕ) :
    (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r] (F*G) =
      F * (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r] G := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz, hF]
    simp only [smul_eq_mul, mul_zero, add_zero, Function.iterate_succ_apply']

variable [Fintype ι]

theorem actual_step_duality (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (j : ι) (F G : MvPolynomial ι ℝ)
    (hF : j ∉ F.vars) :
    mean m hm t ht ((F * MvPolynomial.X j) * G) =
      (((2*m:ℕ):ℝ)*PureOrderPolynomialConditioning.parameters m t j) •
        mean m hm t ht (F *
          (polynomialDerivative (Pi.single j 1) : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[2*m-1] G) := by
  rw [mul_comm F (MvPolynomial.X j), mul_assoc, actual_coordinate_stein,
    iterate_mul_of_derivative_zero _ F G (derivative_zero_of_missing j F hF)]

def stepPolynomial {N : ℕ} (F : Fin N → MvPolynomial (Fin N) ℝ) :
    MvPolynomial (Fin N) ℝ := ∑ j, F j * MvPolynomial.X j

theorem stepPolynomial_eval {N : ℕ} (F : Fin N → MvPolynomial (Fin N) ℝ)
    (x : Fin N → ℝ) :
    MvPolynomial.eval x (stepPolynomial F) = ∑ j, MvPolynomial.eval x (F j) * x j := by
  simp [stepPolynomial]

def Adapted {N : ℕ} (F : Fin N → MvPolynomial (Fin N) ℝ) : Prop :=
  ∀ j, ∀ i ∈ (F j).vars, i < j

theorem adapted_missing {N : ℕ} {F : Fin N → MvPolynomial (Fin N) ℝ}
    (hF : Adapted F) (j : Fin N) : j ∉ (F j).vars := by
  intro hj
  exact (lt_irrefl j) (hF j j hj)

theorem actual_adapted_sum_duality {N : ℕ} (m : ℕ) (hm : 0 < m)
    (t : Fin N → ℝ≥0) (ht : ∀ i, 0 < t i)
    (F : Fin N → MvPolynomial (Fin N) ℝ) (hF : Adapted F)
    (G : MvPolynomial (Fin N) ℝ) :
    mean m hm t ht (stepPolynomial F * G) =
      ∑ j, (((2*m:ℕ):ℝ)*PureOrderPolynomialConditioning.parameters m t j) •
        mean m hm t ht (F j *
          (polynomialDerivative (Pi.single j 1) :
            MvPolynomial (Fin N) ℝ → MvPolynomial (Fin N) ℝ)^[2*m-1] G) := by
  simp only [stepPolynomial, Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl (fun j _ => actual_step_duality m hm t ht j _ G (adapted_missing hF j))

end OperatorDerivativeRewrite.Foundation.HigherHeatAdaptedStepDuality
