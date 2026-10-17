import Foundation.MixedCubicAtomicRealization
import Foundation.FiniteMatrixSpectralMeasure

/-! A sharp attained sixth-moment bound for prescribed moments through degree five. -/
noncomputable section
open MeasureTheory Polynomial Matrix
namespace OperatorDerivativeRewrite.Foundation.MixedCubicSharpSixthMoment
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def boundaryPolynomial (t : ℝ) : Polynomial ℝ :=
  X^3+(4-t) • X^2+(t-7) • X^1+(t-5) • X^0

theorem boundary_square_value (E : Polynomial ℝ →ₗ[ℝ] ℝ) (t : ℝ)
    (h0 : E (X^0) = 1) (h1 : E (X^1) = 0) (h2 : E (X^2) = 1)
    (h3 : E (X^3) = 1) (h4 : E (X^4) = 3) (h5 : E (X^5) = t) :
    E ((boundaryPolynomial t)^2) = E (X^6)-(t^2-8*t+26) := by
  have he : (boundaryPolynomial t)^2 = (X : Polynomial ℝ)^6+
      (2*(4-t)) • X^5+((4-t)^2+2*(t-7)) • X^4+
      (2*(t-5)+2*(4-t)*(t-7)) • X^3+
      ((t-7)^2+2*(4-t)*(t-5)) • X^2+
      (2*(t-7)*(t-5)) • X^1+(t-5)^2 • X^0 := by
    simp only [boundaryPolynomial, Algebra.smul_def, map_add, map_sub, map_mul,
      map_pow, map_ofNat, pow_zero, pow_one]
    ring
  rw [he]
  simp only [map_add, map_smul, smul_eq_mul, h0,h1,h2,h3,h4,h5]
  ring

theorem sixth_moment_lower_bound (E : Polynomial ℝ →ₗ[ℝ] ℝ) (t : ℝ)
    (hpos : ∀ g : Polynomial ℝ, 0 ≤ E (g^2))
    (h0 : E (X^0) = 1) (h1 : E (X^1) = 0) (h2 : E (X^2) = 1)
    (h3 : E (X^3) = 1) (h4 : E (X^4) = 3) (h5 : E (X^5) = t) :
    t^2-8*t+26 ≤ E (X^6) := by
  have h := hpos (boundaryPolynomial t)
  rw [boundary_square_value E t h0 h1 h2 h3 h4 h5] at h
  linarith

def jacobi (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0,1,0; 1,1,1; 0,1,t-5]

theorem jacobi_hermitian (t : ℝ) : (jacobi t).IsHermitian := by
  change (jacobi t).conjTranspose = jacobi t
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacobi, Matrix.conjTranspose_apply]

def extremalLaw (t : ℝ) : Measure ℝ :=
  FiniteMatrixSpectralMeasure.law (jacobi_hermitian t) 0

instance extremalLaw_probability (t : ℝ) : IsProbabilityMeasure (extremalLaw t) :=
  FiniteMatrixSpectralMeasure.law_probability _ _

theorem extremalLaw_integrable (t : ℝ) (f : ℝ → ℝ) : Integrable f (extremalLaw t) :=
  FiniteMatrixSpectralMeasure.law_integrable _ _ _

theorem extremalLaw_moment (t : ℝ) (n : ℕ) :
    (∫ x : ℝ, x^n ∂extremalLaw t) = ((jacobi t)^n) 0 0 :=
  FiniteMatrixSpectralMeasure.law_moment _ _ _

theorem extremalLaw_first_six (t : ℝ) :
    (∫ x : ℝ, x^0 ∂extremalLaw t) = 1 ∧
    (∫ x : ℝ, x^1 ∂extremalLaw t) = 0 ∧
    (∫ x : ℝ, x^2 ∂extremalLaw t) = 1 ∧
    (∫ x : ℝ, x^3 ∂extremalLaw t) = 1 ∧
    (∫ x : ℝ, x^4 ∂extremalLaw t) = 3 ∧
    (∫ x : ℝ, x^5 ∂extremalLaw t) = t ∧
    (∫ x : ℝ, x^6 ∂extremalLaw t) = t^2-8*t+26 := by
  simp only [extremalLaw_moment]
  norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, jacobi, Matrix.one_apply]
  constructor <;> ring

def extremalExpectation (t : ℝ) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun g := ∫ x, g.eval x ∂extremalLaw t
  map_add' P Q := by
    simpa only [eval_add] using integral_add
      (extremalLaw_integrable t (fun x => P.eval x))
      (extremalLaw_integrable t (fun x => Q.eval x))
  map_smul' c P := by
    simp only [eval_smul, smul_eq_mul, integral_const_mul, RingHom.id_apply]

theorem extremalExpectation_apply (t : ℝ) (g : Polynomial ℝ) :
    extremalExpectation t g = ∫ x, g.eval x ∂extremalLaw t := rfl

theorem extremalExpectation_X_pow (t : ℝ) (n : ℕ) :
    extremalExpectation t (X^n) = ∫ x : ℝ, x^n ∂extremalLaw t := by
  change (∫ x, (X^n).eval x ∂extremalLaw t) = _
  simp only [eval_pow, eval_X]

theorem sharp_attained_bound (t : ℝ) :
    ∃ E : Polynomial ℝ →ₗ[ℝ] ℝ,
      (∀ g : Polynomial ℝ, 0 ≤ E (g^2)) ∧
      E (X^0) = 1 ∧ E (X^1) = 0 ∧ E (X^2) = 1 ∧ E (X^3) = 1 ∧
        E (X^4) = 3 ∧ E (X^5) = t ∧ E (X^6) = t^2-8*t+26 := by
  refine ⟨extremalExpectation t, ?_, ?_⟩
  · intro g
    change 0 ≤ ∫ x, (g^2).eval x ∂extremalLaw t
    apply integral_nonneg
    intro x
    simpa only [eval_pow, Pi.zero_apply] using sq_nonneg (g.eval x)
  · simpa only [extremalExpectation_X_pow] using extremalLaw_first_six t

theorem extremal_boundary_square (t : ℝ) :
    (∫ x, ((boundaryPolynomial t).eval x)^2 ∂extremalLaw t) = 0 := by
  have hm := extremalLaw_first_six t
  simp only [← extremalExpectation_X_pow] at hm
  rcases hm with ⟨h0,h1,h2,h3,h4,h5,h6⟩
  have he := boundary_square_value (extremalExpectation t) t h0 h1 h2 h3 h4 h5
  rw [h6, sub_self] at he
  simpa only [extremalExpectation_apply, eval_pow] using he

theorem extremal_boundary_ae (t : ℝ) :
    ∀ᵐ x ∂extremalLaw t, (boundaryPolynomial t).eval x = 0 := by
  have he := (integral_eq_zero_iff_of_nonneg
    (show 0 ≤ fun x => ((boundaryPolynomial t).eval x)^2 from fun x => sq_nonneg _)
    (extremalLaw_integrable t _)).mp (extremal_boundary_square t)
  filter_upwards [he] with x hx
  exact sq_eq_zero_iff.mp hx

end OperatorDerivativeRewrite.Foundation.MixedCubicSharpSixthMoment
