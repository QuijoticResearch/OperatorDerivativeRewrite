import Foundation.MultivariateDirectionalKernel
import Foundation.HigherHeatConditionalRefinement

/-! Exact identification of coordinate heat and zeroing with native signed conditioning. -/
noncomputable section
open scoped BigOperators NNReal
namespace OperatorDerivativeRewrite.Foundation.SingleCoordinateConditioning
open MultivariateDirectionalKernel MultivariateFactorialSubstitution
open PureOrderPolynomialConditioning HigherHeatConditionalRefinement
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def eraseValue (j : ι) (x : ι → ℝ) : ι → ℝ := Function.update x j 0

def eraseWeight (j : ι) (i : ι) : ℝ := if i=j then 0 else 1

def zeroCoordinate (j : ι) : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial ι ℝ :=
  polynomialSubstitution id (eraseWeight j)

def otherProduct (j : ι) (x : ι → ℝ) (d : ι →₀ ℕ) : ℝ :=
  ∏ i ∈ Finset.univ.erase j, x i ^ d i

omit [Fintype ι] in
theorem eval_zeroCoordinate (j : ι) (x : ι → ℝ) (P : MvPolynomial ι ℝ) :
    MvPolynomial.eval x (zeroCoordinate j P) = MvPolynomial.eval (eraseValue j x) P := by
  rw [zeroCoordinate, eval_polynomialSubstitution]
  apply congrArg (fun y : ι → ℝ => MvPolynomial.eval y P)
  funext i
  by_cases hi : i=j <;> simp [eraseValue, eraseWeight, hi]

theorem line_monomial (j : ι) (x : ι → ℝ) (d : ι →₀ ℕ) (c : ℝ) :
    line (Pi.single j 1) (eraseValue j x) (MvPolynomial.monomial d c) =
      Polynomial.monomial (d j) (c * otherProduct j x d) := by
  apply Polynomial.funext
  intro z
  rw [eval_line, MvPolynomial.eval_monomial, Polynomial.eval_monomial,
    Finsupp.prod_fintype d _ (fun _ => pow_zero _)]
  have he : (∏ i, (eraseValue j x i + z * (Pi.single j (1:ℝ) : ι → ℝ) i)^d i) =
      z^(d j) * otherProduct j x d := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => (eraseValue j x i + z * (Pi.single j (1:ℝ) : ι → ℝ) i)^d i)
      (Finset.mem_univ j)]
    simp only [eraseValue, Function.update_self, Pi.single_eq_same, zero_add, mul_one]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hne : i ≠ j := (Finset.mem_erase.mp hi).1
    simp [hne]
  rw [he]
  ring

theorem factor_one_future (p : ℕ) (a : ι → ℝ) (j : ι) (d : ι →₀ ℕ) :
    factor p a (Finset.univ.erase j) d = PseudoPolynomialStein.moment p (a j) (d j) := by
  rw [factor, Finset.prod_eq_single j]
  · simp
  · intro i hi hne
    simp [hne]
  · simp

theorem pastValue_one_future (j : ι) (x : ι → ℝ) (d : ι →₀ ℕ) :
    pastValue (Finset.univ.erase j) x d = otherProduct j x d := by
  calc
    pastValue (Finset.univ.erase j) x d =
        ∏ i ∈ Finset.univ.erase j, if i ∈ Finset.univ.erase j then x i^d i else 1 := by
      unfold pastValue
      convert (Finset.prod_subset
        (f := fun i : ι => if i ∈ Finset.univ.erase j then x i^d i else (1:ℝ))
        (Finset.subset_univ (Finset.univ.erase j))
        (fun i hi hni => ite_eq_right hni)).symm using 1
      apply Finset.prod_congr rfl
      intro i hi
      by_cases h : i ∈ Finset.univ.erase j <;> simp [h]
    _ = otherProduct j x d := by
      apply Finset.prod_congr rfl
      intro i hi
      exact ite_eq_left hi

theorem conditioning_monomial_eval (p : ℕ) (a : ι → ℝ) (j : ι) (x : ι → ℝ)
    (d : ι →₀ ℕ) (c : ℝ) :
    MvPolynomial.eval x (conditioning p a (Finset.univ.erase j) (MvPolynomial.monomial d c)) =
      (c * otherProduct j x d) * PseudoPolynomialStein.moment p (a j) (d j) := by
  rw [conditioning_monomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), kept_value,
    factor_one_future, pastValue_one_future]
  ring

theorem heat_then_zero (p : ℕ) (hp : 0 < p) (a : ι → ℝ) (j : ι) (P : MvPolynomial ι ℝ) :
    zeroCoordinate j (transport p hp (a j) (Pi.single j 1) P) =
      conditioning p a (Finset.univ.erase j) P := by
  apply MvPolynomial.funext
  intro x
  rw [eval_zeroCoordinate]
  change MvPolynomial.eval (eraseValue j x)
    (MultivariateFactorialHeat.polynomialEvolution p (a j) (Pi.single j 1) P) = _
  rw [← expectation_polynomialEvolution p hp]
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [line_monomial, PseudoPolynomialStein.expectation_monomial, conditioning_monomial_eval]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

end OperatorDerivativeRewrite.Foundation.SingleCoordinateConditioning
