import Foundation.MultivariateFactorialDomain
import Foundation.PureOrderPolynomialConditioning
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Actual signed polynomial conditioning commutes with derivatives in
retained coordinates. This statement is not true in discarded coordinates. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RetainedCoordinateDifferentiation
open PureOrderPolynomialConditioning MultivariateFactorialDomain
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem keep_sub_axis (S : Finset ι) (j : ι) (hj : j ∈ S) (d : ι →₀ ℕ) :
    keep S (d - Finsupp.single j 1) = keep S d - Finsupp.single j 1 := by
  ext i
  by_cases hi : i ∈ S <;> by_cases he : i=j <;>
    simp_all [keep_apply, Finsupp.tsub_apply, Finsupp.single_apply]

private theorem factor_sub_axis (p : ℕ) (a : ι → ℝ) (S : Finset ι)
    (j : ι) (hj : j ∈ S) (d : ι →₀ ℕ) :
    factor p a S (d - Finsupp.single j 1) = factor p a S d := by
  unfold factor
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp [hi]
  · have he : i ≠ j := by intro h; subst i; exact hi hj
    simp [hi, Finsupp.tsub_apply, Finsupp.single_apply, he]

omit [Fintype ι] in
theorem axis_derivative_eq_pderiv (j : ι) :
    polynomialDerivative (Pi.single j 1) = MvPolynomial.pderiv j := by
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialDerivative, MvPolynomial.mkDerivation_X, MvPolynomial.pderiv_X]
  by_cases h : i=j <;> simp [Pi.single_apply, h]

theorem pderiv_conditioning (p : ℕ) (a : ι → ℝ) (S : Finset ι)
    (j : ι) (hj : j ∈ S) (P : MvPolynomial ι ℝ) :
    MvPolynomial.pderiv j (conditioning p a S P) =
      conditioning p a S (MvPolynomial.pderiv j P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [conditioning_monomial, MvPolynomial.pderiv_monomial,
      MvPolynomial.pderiv_monomial, conditioning_monomial,
      keep_sub_axis S j hj d, factor_sub_axis p a S j hj d, keep_apply, if_pos hj]
    congr 1
    ring
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem derivative_conditioning (p : ℕ) (a : ι → ℝ) (S : Finset ι)
    (j : ι) (hj : j ∈ S) (P : MvPolynomial ι ℝ) :
    polynomialDerivative (Pi.single j 1) (conditioning p a S P) =
      conditioning p a S (polynomialDerivative (Pi.single j 1) P) := by
  rw [axis_derivative_eq_pderiv]
  exact pderiv_conditioning p a S j hj P

theorem iterate_conditioning (p : ℕ) (a : ι → ℝ) (S : Finset ι)
    (j : ι) (hj : j ∈ S) (q : ℕ) (P : MvPolynomial ι ℝ) :
    (polynomialDerivative (Pi.single j 1) : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[q]
        (conditioning p a S P) =
      conditioning p a S
        ((polynomialDerivative (Pi.single j 1) : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[q] P) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply', ih, derivative_conditioning p a S j hj,
      Function.iterate_succ_apply']

end OperatorDerivativeRewrite.Foundation.RetainedCoordinateDifferentiation
