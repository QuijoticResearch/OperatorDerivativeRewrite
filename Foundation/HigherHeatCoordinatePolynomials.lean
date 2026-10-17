import Foundation.HigherHeatProductPolynomials

/-! Actual one-coordinate and distinct-coordinate polynomial moments of signed increment laws. -/
noncomputable section
open MeasureTheory Polynomial
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCoordinatePolynomials
open HigherHeatSignedLaws HigherHeatPolynomialRealization HigherHeatProductPolynomials

variable {ι : Type*} [Fintype ι]

def atPolynomial (i : ι) (P : Polynomial ℝ) (j : ι) : Polynomial ℝ := by
  classical
  exact if j = i then P else 1

theorem observable_at (i : ι) (P : Polynomial ℝ) (x : ι → ℝ) :
    observable (atPolynomial i P) x = ((P.eval (x i) : ℝ) : ℂ) := by
  classical
  simp [observable, atPolynomial, apply_ite]

theorem observable_mul (P Q : ι → Polynomial ℝ) (x : ι → ℝ) :
    observable (fun i => P i * Q i) x = observable P x * observable Q x := by
  simp only [observable, eval_mul, Complex.ofReal_mul, Finset.prod_mul_distrib]

theorem coordinate_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (i : ι) (P : Polynomial ℝ) :
    (incrementLaw m hm t ht).Integrable (fun x => ((P.eval (x i) : ℝ) : ℂ)) := by
  have he : observable (atPolynomial i P) = (fun x => ((P.eval (x i) : ℝ) : ℂ)) :=
    funext (observable_at i P)
  rw [← he]
  exact product_signed_integrable m hm t ht (atPolynomial i P)

theorem coordinate_integral (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (i : ι) (P : Polynomial ℝ) :
    (∫ᵛ x, ((P.eval (x i) : ℝ) : ℂ) ∂<•incrementLaw m hm t ht) =
      (kernelExpectation m hm (t i) (ht i) P : ℂ) := by
  classical
  have he := product_signed_integral m hm t ht (atPolynomial i P)
  simpa only [observable_at, atPolynomial, apply_ite, kernelExpectation_one,
    Complex.ofReal_one, Fintype.prod_ite_eq'] using he

theorem mixed_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (i j : ι) (P Q : Polynomial ℝ) :
    (incrementLaw m hm t ht).Integrable
      (fun x => ((P.eval (x i) : ℝ) : ℂ) * ((Q.eval (x j) : ℝ) : ℂ)) := by
  have he : observable (fun l => atPolynomial i P l * atPolynomial j Q l) =
      (fun x => ((P.eval (x i) : ℝ) : ℂ) * ((Q.eval (x j) : ℝ) : ℂ)) := by
    funext x
    rw [observable_mul, observable_at, observable_at]
  rw [← he]
  exact product_signed_integrable m hm t ht (fun l => atPolynomial i P l * atPolynomial j Q l)

theorem mixed_integral (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (i j : ι) (hij : i ≠ j) (P Q : Polynomial ℝ) :
    (∫ᵛ x, ((P.eval (x i) : ℝ) : ℂ) * ((Q.eval (x j) : ℝ) : ℂ)
      ∂<•incrementLaw m hm t ht) =
      (kernelExpectation m hm (t i) (ht i) P : ℂ) *
        (kernelExpectation m hm (t j) (ht j) Q : ℂ) := by
  classical
  have he := product_signed_integral m hm t ht
    (fun l => atPolynomial i P l * atPolynomial j Q l)
  simp only [observable_mul, observable_at] at he
  rw [he]
  have hh (l : ι) : (kernelExpectation m hm (t l) (ht l)
      (atPolynomial i P l * atPolynomial j Q l) : ℂ) =
      (if l = i then (kernelExpectation m hm (t i) (ht i) P : ℂ) else 1) *
      (if l = j then (kernelExpectation m hm (t j) (ht j) Q : ℂ) else 1) := by
    by_cases hli : l = i
    · subst l
      simp [atPolynomial, hij, kernelExpectation_one]
    · by_cases hlj : l = j
      · subst l
        simp [atPolynomial, hij.symm, kernelExpectation_one]
      · simp [atPolynomial, hli, hlj, kernelExpectation_one]
  simp_rw [hh]
  rw [Finset.prod_mul_distrib]
  simp

end OperatorDerivativeRewrite.Foundation.HigherHeatCoordinatePolynomials
