import Foundation.PseudoPolynomialStein
import Foundation.GaussianCore

/-! Exact positivity classification and actual Gaussian realization of pure-order moments. -/
noncomputable section
open MeasureTheory Polynomial
namespace OperatorDerivativeRewrite.Foundation.PseudoMomentGaussianBoundary
open PseudoPolynomialStein GaussianCore
set_option backward.isDefEq.respectTransparency false

theorem scaled_polynomial_integrable (h : ℝ) (g : Polynomial ℝ) :
    Integrable (fun x => g.eval (h*x)) γ := by
  simpa only [coordinatePolynomial_eval, W] using
    (GaussianCore.polynomial_memLp (coordinatePolynomial h g) 1 (by simp)).integrable (by simp)

def gaussianExpectation (h : ℝ) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun g := ∫ x, g.eval (h*x) ∂γ
  map_add' P Q := by
    simpa only [eval_add] using integral_add
      (scaled_polynomial_integrable h P) (scaled_polynomial_integrable h Q)
  map_smul' c P := by
    simp only [eval_smul, smul_eq_mul, integral_const_mul, RingHom.id_apply]

theorem gaussianExpectation_apply (h : ℝ) (g : Polynomial ℝ) :
    gaussianExpectation h g = ∫ x, g.eval (h*x) ∂γ := rfl

theorem gaussianExpectation_one (h : ℝ) : gaussianExpectation h 1 = 1 := by
  simp [gaussianExpectation]

theorem gaussianExpectation_stein (h : ℝ) (g : Polynomial ℝ) :
    gaussianExpectation h (X*g) = h^2 * gaussianExpectation h g.derivative := by
  have hd : (coordinatePolynomial h g).derivative = h • coordinatePolynomial h g.derivative := by
    simp only [coordinatePolynomial, derivative_comp, derivative_mul, derivative_C,
      derivative_X, zero_mul, mul_one, zero_add, smul_eq_C_mul]
  calc
    gaussianExpectation h (X*g) =
        h * ∫ x, (coordinatePolynomial h g).eval x * x ∂γ := by
      change (∫ x, (X*g).eval (h*x) ∂γ) = _
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [eval_mul, eval_X, coordinatePolynomial_eval, W]
        ring
    _ = h * ∫ x, (coordinatePolynomial h g).derivative.eval x ∂γ := by
      rw [GaussianCore.polynomial_stein]
    _ = h^2 * gaussianExpectation h g.derivative := by
      rw [hd]
      simp only [eval_smul, smul_eq_mul, coordinatePolynomial_eval, W,
        integral_const_mul, gaussianExpectation_apply]
      ring

theorem gaussianExpectation_eq_expectation (h : ℝ) :
    gaussianExpectation h = expectation 2 (h^2/2) := by
  apply expectation_unique 2 (h^2/2) _ (gaussianExpectation_one h)
  intro g
  simpa only [Nat.reduceSub, Function.iterate_one, Nat.cast_ofNat,
    show (2 : ℝ)*(h^2/2) = h^2 by ring] using gaussianExpectation_stein h g

theorem expectation_standard_gaussian (g : Polynomial ℝ) :
    expectation 2 (1/2) g = ∫ x, g.eval x ∂γ := by
  have he := congrArg (fun E : Polynomial ℝ →ₗ[ℝ] ℝ => E g)
    (gaussianExpectation_eq_expectation 1).symm
  simpa [gaussianExpectation] using he

theorem expectation_nonnegative_gaussian (a : ℝ) (ha : 0 ≤ a) (g : Polynomial ℝ) :
    expectation 2 a g = ∫ x, g.eval (Real.sqrt (2*a)*x) ∂γ := by
  have hs : (Real.sqrt (2*a))^2/2 = a := by rw [Real.sq_sqrt (by positivity)]; ring
  have he := congrArg (fun E : Polynomial ℝ →ₗ[ℝ] ℝ => E g)
    (gaussianExpectation_eq_expectation (Real.sqrt (2*a))).symm
  simpa only [hs, gaussianExpectation_apply] using he

theorem gaussianExpectation_square_nonneg (h : ℝ) (g : Polynomial ℝ) :
    0 ≤ gaussianExpectation h (g^2) := by
  change 0 ≤ ∫ x, (g^2).eval (h*x) ∂γ
  apply integral_nonneg
  intro x
  simpa only [eval_pow, Pi.zero_apply] using sq_nonneg (g.eval (h*x))

theorem expectation_two_square_nonneg (a : ℝ) (ha : 0 ≤ a) (g : Polynomial ℝ) :
    0 ≤ expectation 2 a (g^2) := by
  rw [expectation_nonnegative_gaussian a ha]
  apply integral_nonneg
  intro x
  simpa only [eval_pow, Pi.zero_apply] using sq_nonneg (g.eval (Real.sqrt (2*a)*x))

theorem expectation_zero_eval (p : ℕ) (g : Polynomial ℝ) :
    expectation p 0 g = g.eval 0 := by
  have he := expectation_unique p 0 (aeval (0 : ℝ)).toLinearMap (by simp)
    (by intro Q; simp)
  simpa using congrArg (fun E : Polynomial ℝ →ₗ[ℝ] ℝ => E g) he.symm

theorem square_positive_iff (p : ℕ) (hp : 2 ≤ p) (a : ℝ) :
    (∀ g : Polynomial ℝ, 0 ≤ expectation p a (g^2)) ↔
      a = 0 ∨ p = 2 ∧ 0 ≤ a := by
  constructor
  · intro hpos
    by_cases ha : a = 0
    · exact Or.inl ha
    · have hp2 : p = 2 := by
        by_contra hne
        exact expectation_not_positive p (by omega) a ha hpos
      refine Or.inr ⟨hp2, ?_⟩
      subst p
      have hx := hpos X
      rw [expectation_X_pow, moment_leading 2 (by omega)] at hx
      norm_num at hx
      linarith
  · rintro (rfl | ⟨rfl, ha⟩)
    · intro g
      rw [expectation_zero_eval, eval_pow]
      exact sq_nonneg _
    · exact expectation_two_square_nonneg a ha

theorem square_positive_iff_gaussian_realizable (p : ℕ) (hp : 2 ≤ p) (a : ℝ) :
    (∀ g : Polynomial ℝ, 0 ≤ expectation p a (g^2)) ↔
      ∃ h : ℝ, expectation p a = gaussianExpectation h := by
  constructor
  · intro hpos
    rcases (square_positive_iff p hp a).mp hpos with rfl | ⟨rfl, ha⟩
    · refine ⟨0, ?_⟩
      apply LinearMap.ext
      intro g
      simp [expectation_zero_eval, gaussianExpectation]
    · refine ⟨Real.sqrt (2*a), ?_⟩
      apply LinearMap.ext
      intro g
      exact expectation_nonnegative_gaussian a ha g
  · rintro ⟨h, he⟩ g
    rw [he]
    exact gaussianExpectation_square_nonneg h g

theorem gaussian_square_eq_zero_iff (h : ℝ) (hh : h ≠ 0) (g : Polynomial ℝ) :
    gaussianExpectation h (g^2) = 0 ↔ g = 0 := by
  constructor
  · intro hz
    rw [gaussianExpectation_apply] at hz
    have hae := (integral_eq_zero_iff_of_nonneg
      (show 0 ≤ fun x => (g^2).eval (h*x) from fun x => by
        simpa only [eval_pow, Pi.zero_apply] using sq_nonneg (g.eval (h*x)))
      (scaled_polynomial_integrable h (g^2))).mp hz
    have hg : (fun x => g.eval (h*x)) =ᵐ[γ] 0 := hae.mono fun x hx => by
      change g.eval (h*x) = 0
      apply sq_eq_zero_iff.mp
      simpa only [eval_pow, Pi.zero_apply] using hx
    have he := continuous_representation_unique
      (g.continuous.comp (continuous_const.mul continuous_id)) continuous_const hg
    apply Polynomial.funext
    intro y
    have hy := congrFun he (y/h)
    change g.eval (h*(y/h)) = 0 at hy
    have hmul : h*(y/h) = y := by field_simp
    simpa only [hmul, eval_zero] using hy
  · rintro rfl
    simp [gaussianExpectation_apply]

theorem gaussian_square_strict (h : ℝ) (hh : h ≠ 0) (g : Polynomial ℝ) (hg : g ≠ 0) :
    0 < gaussianExpectation h (g^2) := by
  have hn : gaussianExpectation h (g^2) ≠ 0 := by
    intro hz
    exact hg ((gaussian_square_eq_zero_iff h hh g).mp hz)
  exact lt_of_le_of_ne (gaussianExpectation_square_nonneg h g) hn.symm

theorem square_strictly_positive_iff (p : ℕ) (hp : 2 ≤ p) (a : ℝ) :
    (∀ g : Polynomial ℝ, g ≠ 0 → 0 < expectation p a (g^2)) ↔
      p = 2 ∧ 0 < a := by
  constructor
  · intro hstrict
    have ha0 : a ≠ 0 := by
      intro hz
      have hx := hstrict X X_ne_zero
      rw [hz, expectation_zero_eval] at hx
      norm_num at hx
    have hpos : ∀ g : Polynomial ℝ, 0 ≤ expectation p a (g^2) := by
      intro g
      by_cases hg : g = 0
      · simp [hg]
      · exact (hstrict g hg).le
    rcases (square_positive_iff p hp a).mp hpos with hz | ⟨hp2, ha⟩
    · exact (ha0 hz).elim
    · exact ⟨hp2, lt_of_le_of_ne ha ha0.symm⟩
  · rintro ⟨rfl, ha⟩ g hg
    rw [expectation_nonnegative_gaussian a ha.le]
    change 0 < gaussianExpectation (Real.sqrt (2*a)) (g^2)
    exact gaussian_square_strict _ (ne_of_gt (Real.sqrt_pos.mpr (by positivity))) g hg

end OperatorDerivativeRewrite.Foundation.PseudoMomentGaussianBoundary
