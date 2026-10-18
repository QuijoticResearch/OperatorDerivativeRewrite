import Foundation.HigherHeatProductPolynomials

/-! Separated chronological increments refute a nonzero signed second-moment isometry.
These are actual finite signed laws, with integrability proved before integration. -/
noncomputable section
open MeasureTheory Polynomial
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatChronologicalObstruction
open HigherHeatSignedLaws HigherHeatPolynomialRealization HigherHeatProductPolynomials

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def separatedProduct (x : ι → ℝ) : ℂ := ∏ i, (x i : ℂ)

omit [Nonempty ι] in
theorem power_eq_observable (x : ι → ℝ) (d : ℕ) :
    separatedProduct x ^ d = observable (fun _ : ι => (X : Polynomial ℝ)^d) x := by
  simp [separatedProduct, observable, Finset.prod_pow]

omit [Nonempty ι] in
theorem power_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (d : ℕ) :
    (incrementLaw m hm t ht).Integrable (fun x => separatedProduct x ^ d) := by
  simp_rw [power_eq_observable]
  exact product_signed_integrable m hm t ht _

theorem square_zero (m : ℕ) (hm : 2 ≤ m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) :
    (∫ᵛ x, separatedProduct x ^ 2 ∂<•incrementLaw m (by omega) t ht) = 0 := by
  simp_rw [power_eq_observable]
  rw [product_signed_integral]
  have hi (i : ι) : kernelExpectation m (by omega) (t i) (ht i) (X^2) = 0 := by
    rw [kernelExpectation_eq_moments, PseudoPolynomialStein.expectation_X_pow]
    apply PseudoPolynomialStein.moment_off_order (2*m) (by omega)
    intro h
    have hh := Nat.le_of_dvd (by norm_num : 0 < (2:ℕ)) h
    omega
  simp [hi]

omit [Nonempty ι] in
theorem leading_power_ne_zero (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) :
    (∫ᵛ x, separatedProduct x ^ (2*m) ∂<•incrementLaw m hm t ht) ≠ 0 := by
  simp_rw [power_eq_observable]
  rw [product_signed_integral]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Complex.ofReal_ne_zero.mpr
  rw [kernelExpectation_eq_moments, PseudoPolynomialStein.expectation_X_pow,
    PseudoPolynomialStein.moment_leading (2*m) (by omega)]
  exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (2*m))
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (ht i)))

omit [Nonempty ι] in
theorem paired_power_ne_zero (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) :
    (∫ᵛ x, separatedProduct x * separatedProduct x ^ (2*m-1)
      ∂<•incrementLaw m hm t ht) ≠ 0 := by
  have he : 2*m-1+1=2*m := by omega
  simp_rw [← pow_succ', he]
  exact leading_power_ne_zero m hm t ht

theorem no_nonzero_diagonal_isometry (m : ℕ) (hm : 2 ≤ m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (γ energy : ℂ) (hγ : γ ≠ 0) (hE : energy ≠ 0) :
    (∫ᵛ x, separatedProduct x ^ 2 ∂<•incrementLaw m (by omega) t ht) ≠ γ * energy := by
  rw [square_zero m hm t ht]
  exact Ne.symm (mul_ne_zero hγ hE)

end OperatorDerivativeRewrite.Foundation.HigherHeatChronologicalObstruction
