import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-! Independent diagnostics for Incoming manuscript claims. No manuscript theorem
is an assumption. The Schur examples are scalar blocks with interior block one.
The polynomial obstruction concerns square positivity, not signed integration. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.ManuscriptSchurDiagnostics

def schur (a b c : ℝ) : ℝ := a - b ^ 2 / c

/-- The stated general stability estimate fails even for positive-definite blocks:
H₀ = [[2,1],[1,1]], H = [[2,11/10],[11/10,1]]. -/
theorem general_stability_counterexample :
    0 < schur 2 1 1 ∧ 0 < schur 2 (11/10) 1 ∧
      schur 2 (11/10) 1 < schur 2 1 1 - 4 * (1/10 : ℝ)^2 := by
  norm_num [schur]

/-- An arbitrarily small positive coupling perturbation defeats the same bound. -/
theorem small_coupling_counterexample (d : ℝ) (hd : 0 < d) (hd' : d < 2/3) :
    schur 2 (1+d) 1 < schur 2 1 1 - 4*d^2 := by
  simp only [schur, div_one]
  nlinarith

theorem fixed_interior_increment (a b d : ℝ) :
    schur a (b+d) 1 = schur a b 1 - 2*b*d - d^2 := by
  simp only [schur, div_one]
  ring

/-- Correct perturbation loss with fixed unit interior, including the cross term. -/
theorem fixed_interior_lower_bound (a b d eta : ℝ) (hd : |d| ≤ eta) :
    schur a b 1 - (2 * |b| * eta + eta^2) ≤ schur a (b+d) 1 := by
  have he : 0 ≤ eta := (abs_nonneg d).trans hd
  have hp : b*d ≤ |b| * eta :=
    (le_abs_self (b*d)).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hd (abs_nonneg b))
  have hs : d^2 ≤ eta^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg d) hd
    simpa only [← sq, sq_abs] using hh
  rw [fixed_interior_increment]
  nlinarith

/-- The zero-coupling application does not suffer the missing linear loss. -/
theorem zero_coupling_lower_bound (a d eta : ℝ) (hd : |d| ≤ eta) :
    a - eta^2 ≤ schur a d 1 := by
  simpa [schur] using fixed_interior_lower_bound a 0 d eta hd

/-- A negative fourth moment is incompatible with any square-positive
polynomial functional. This does not preclude an indefinite pseudo-expectation. -/
theorem negative_fourth_moment_not_positive
    (expect : Polynomial ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hfour : expect (Polynomial.X^4) = -24*T) :
    ¬ (∀ p : Polynomial ℝ, 0 ≤ expect (p^2)) := by
  intro hpos
  have h := hpos (Polynomial.X^2)
  have he : ((Polynomial.X : Polynomial ℝ)^2)^2 = Polynomial.X^4 := by ring
  rw [he, hfour] at h
  linarith

end OperatorDerivativeRewrite.Foundation.ManuscriptSchurDiagnostics
