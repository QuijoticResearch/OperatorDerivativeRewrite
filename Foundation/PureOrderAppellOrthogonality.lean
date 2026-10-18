import Foundation.PureOrderAppellPairing
import Foundation.PureOrderAppellTail
import Foundation.GaussianHermite

/-! A uniform off-diagonal Appell probe at every non-Gaussian pure order. -/
noncomputable section
open Polynomial
namespace OperatorDerivativeRewrite.Foundation.PureOrderAppellOrthogonality
open PureOrderAppellCalculus PureOrderAppellPairing PseudoClarkOconeObstruction

theorem appell_one (p : ℕ) (hp : 1 < p) (a : ℝ) : appell p a 1 = X := by
  simp [appell, raise, iterate_derivative_one (by omega : 0 < p-1)]

theorem complementary_pair_ne_zero (p : ℕ) (hp : 1 < p) (a : ℝ) (ha : a ≠ 0) :
    pairing p a (appell p a (p-1)) (appell p a 1) ≠ 0 := by
  have he := polynomial_top_ne_zero p hp a ha (X : Polynomial ℝ) X_ne_zero
  simpa only [natDegree_X, mul_one, appell_one p hp a] using he

theorem not_orthogonal (p : ℕ) (hp : 2 < p) (a : ℝ) (ha : a ≠ 0) :
    ¬ ∀ n k : ℕ, n ≠ k → pairing p a (appell p a n) (appell p a k) = 0 := by
  intro h
  exact complementary_pair_ne_zero p (by omega) a ha (h (p-1) 1 (by omega))


theorem gaussian_appell (n : ℕ) : appell 2 (1/2:ℝ) n = GaussianCore.hermitePolynomial n := by
  induction n with
  | zero => simp [appell]
  | succ n ih =>
    rw [appell, raise, ih, GaussianCore.hermitePolynomial_succ]
    norm_num [GaussianCore.divergencePolynomial]

theorem gaussian_inner (n k : ℕ) :
    inner ℝ (GaussianCore.polynomialL2 (appell 2 (1/2:ℝ) n))
      (GaussianCore.polynomialL2 (appell 2 (1/2:ℝ) k)) =
      if n=k then (n.factorial:ℝ) else 0 := by
  rw [gaussian_appell, gaussian_appell]
  exact GaussianCore.hermiteVector_inner n k

def gaussianExpectation : Polynomial ℝ →ₗ[ℝ] ℝ :=
  (innerSL ℝ (GaussianCore.polynomialL2 1)).toLinearMap.comp GaussianCore.polynomialEmbedding

theorem gaussianExpectation_eq : gaussianExpectation =
    PseudoPolynomialStein.expectation 2 (1/2:ℝ) := by
  apply (PureOrderAppellExpansion.basis 2 (1/2:ℝ)).ext
  intro n
  rw [PureOrderAppellExpansion.basis_apply]
  change inner ℝ (GaussianCore.polynomialL2 1)
    (GaussianCore.polynomialL2 (appell 2 (1/2:ℝ) n)) = _
  have hm := PureOrderAppellExpansion.coordinate_appell 2 (1/2:ℝ) 0 n
  rw [PureOrderAppellTail.coordinate_zero] at hm
  rw [hm]
  have h := gaussian_inner 0 n
  simpa only [appell, Nat.factorial_zero, Nat.cast_one, eq_comm] using h

theorem gaussian_pairing (n k : ℕ) :
    pairing 2 (1/2:ℝ) (appell 2 (1/2:ℝ) n) (appell 2 (1/2:ℝ) k) =
      if n=k then (n.factorial:ℝ) else 0 := by
  rw [pairing, ← gaussianExpectation_eq]
  change inner ℝ (GaussianCore.polynomialL2 1)
    (GaussianCore.polynomialL2 ((appell 2 (1/2:ℝ) n)*(appell 2 (1/2:ℝ) k))) = _
  rw [GaussianCore.polynomialL2_inner]
  simp only [eval_one, one_mul, eval_mul]
  have h := gaussian_inner n k
  rw [GaussianCore.polynomialL2_inner] at h
  exact h

theorem normalized_orthogonal_iff (p : ℕ) (hp : 1 < p) :
    (∀ n k : ℕ, n ≠ k → pairing p (1/2:ℝ) (appell p (1/2:ℝ) n)
      (appell p (1/2:ℝ) k) = 0) ↔ p=2 := by
  constructor
  · intro h
    by_contra hn
    exact not_orthogonal p (by omega) (1/2:ℝ) (by norm_num) h
  · intro h
    subst p
    intro n k hn
    rw [gaussian_pairing, ite_eq_right hn]

end OperatorDerivativeRewrite.Foundation.PureOrderAppellOrthogonality
