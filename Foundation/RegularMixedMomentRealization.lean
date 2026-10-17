import Foundation.MixedCubicSharpSixthMoment

/-! Sharp attained sixth moments for regular mixed variance/skewness data. -/
noncomputable section
open MeasureTheory Polynomial Matrix
namespace OperatorDerivativeRewrite.Foundation.RegularMixedMomentRealization
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def delta (v k : ℝ) : ℝ := 2*v^3-k^2
def alpha (v k t : ℝ) : ℝ := v*(t-4*v*k)/delta v k
def beta (v k t : ℝ) : ℝ := 3*v-k*(t-4*v*k)/delta v k
def gamma (v k t : ℝ) : ℝ := k-v^2*(t-4*v*k)/delta v k
def floor (v k t : ℝ) : ℝ := 9*v^3+k^2+v*(t-4*v*k)^2/delta v k
def boundaryPolynomial (v k t : ℝ) : Polynomial ℝ :=
  X^3-alpha v k t • X^2-beta v k t • X^1-gamma v k t • X^0

theorem boundary_square_value (E : Polynomial ℝ →ₗ[ℝ] ℝ) (v k t : ℝ)
    (hd : delta v k ≠ 0)
    (h0 : E (X^0) = 1) (h1 : E (X^1) = 0) (h2 : E (X^2) = v)
    (h3 : E (X^3) = k) (h4 : E (X^4) = 3*v^2) (h5 : E (X^5) = t) :
    E ((boundaryPolynomial v k t)^2) = E (X^6)-floor v k t := by
  have he : (boundaryPolynomial v k t)^2 = (X : Polynomial ℝ)^6+
      (-2*alpha v k t) • X^5+((alpha v k t)^2-2*beta v k t) • X^4+
      (2*alpha v k t*beta v k t-2*gamma v k t) • X^3+
      ((beta v k t)^2+2*alpha v k t*gamma v k t) • X^2+
      (2*beta v k t*gamma v k t) • X^1+(gamma v k t)^2 • X^0 := by
    simp only [boundaryPolynomial, Algebra.smul_def, map_add, map_sub, map_mul, map_neg,
      map_pow, map_ofNat, pow_zero, pow_one]
    ring
  rw [he]
  simp only [map_add, map_smul, smul_eq_mul, h0,h1,h2,h3,h4,h5]
  dsimp [alpha,beta,gamma,floor]
  field_simp [hd]
  dsimp [delta]
  ring

theorem sixth_moment_lower_bound (E : Polynomial ℝ →ₗ[ℝ] ℝ) (v k t : ℝ)
    (hd : delta v k ≠ 0) (hpos : ∀ g : Polynomial ℝ, 0 ≤ E (g^2))
    (h0 : E (X^0) = 1) (h1 : E (X^1) = 0) (h2 : E (X^2) = v)
    (h3 : E (X^3) = k) (h4 : E (X^4) = 3*v^2) (h5 : E (X^5) = t) :
    floor v k t ≤ E (X^6) := by
  have h := hpos (boundaryPolynomial v k t)
  rw [boundary_square_value E v k t hd h0 h1 h2 h3 h4 h5] at h
  linarith

def tailDiagonal (v k t : ℝ) : ℝ := (v^2*t-6*v^3*k+k^3)/(v*delta v k)
def jacobi (v k t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0,Real.sqrt v,0;
     Real.sqrt v,k/v,Real.sqrt (delta v k)/v;
     0,Real.sqrt (delta v k)/v,tailDiagonal v k t]

theorem jacobi_hermitian (v k t : ℝ) : (jacobi v k t).IsHermitian := by
  change (jacobi v k t).conjTranspose = jacobi v k t
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacobi, Matrix.conjTranspose_apply]

def extremalLaw (v k t : ℝ) : Measure ℝ :=
  FiniteMatrixSpectralMeasure.law (jacobi_hermitian v k t) 0

instance extremalLaw_probability (v k t : ℝ) : IsProbabilityMeasure (extremalLaw v k t) :=
  FiniteMatrixSpectralMeasure.law_probability _ _

theorem extremalLaw_integrable (v k t : ℝ) (f : ℝ → ℝ) :
    Integrable f (extremalLaw v k t) := FiniteMatrixSpectralMeasure.law_integrable _ _ _

theorem extremalLaw_moment (v k t : ℝ) (n : ℕ) :
    (∫ x : ℝ, x^n ∂extremalLaw v k t) = ((jacobi v k t)^n) 0 0 :=
  FiniteMatrixSpectralMeasure.law_moment _ _ _

theorem extremalLaw_first_seven (v k t : ℝ) (hv : 0 < v) (hd : 0 < delta v k) :
    (∫ x : ℝ, x^0 ∂extremalLaw v k t) = 1 ∧
    (∫ x : ℝ, x^1 ∂extremalLaw v k t) = 0 ∧
    (∫ x : ℝ, x^2 ∂extremalLaw v k t) = v ∧
    (∫ x : ℝ, x^3 ∂extremalLaw v k t) = k ∧
    (∫ x : ℝ, x^4 ∂extremalLaw v k t) = 3*v^2 ∧
    (∫ x : ℝ, x^5 ∂extremalLaw v k t) = t ∧
    (∫ x : ℝ, x^6 ∂extremalLaw v k t) = floor v k t := by
  have hv2 := Real.sq_sqrt hv.le
  have hd2 := Real.sq_sqrt hd.le
  have hv4 : (Real.sqrt v)^4 = v^2 := by nlinarith [sq_nonneg ((Real.sqrt v)^2-v)]
  have hd4 : (Real.sqrt (delta v k))^4 = (delta v k)^2 := by
    nlinarith [sq_nonneg ((Real.sqrt (delta v k))^2-delta v k)]
  have hv6 : (Real.sqrt v)^6 = v^3 := by
    calc
      _ = ((Real.sqrt v)^2)^3 := by ring
      _ = _ := by rw [hv2]
  simp only [extremalLaw_moment]
  norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, jacobi, Matrix.one_apply]
  repeat' constructor
  all_goals
    (try simp only [tailDiagonal,floor]) <;> ring_nf <;>
      (try simp only [hv2,hd2,hv4,hd4,hv6]) <;>
      (try field_simp [hv.ne',hd.ne']) <;> (try simp only [delta]) <;> ring

def extremalExpectation (v k t : ℝ) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun g := ∫ x, g.eval x ∂extremalLaw v k t
  map_add' P Q := by
    simpa only [eval_add] using integral_add
      (extremalLaw_integrable v k t (fun x => P.eval x))
      (extremalLaw_integrable v k t (fun x => Q.eval x))
  map_smul' c P := by
    simp only [eval_smul, smul_eq_mul, integral_const_mul, RingHom.id_apply]

theorem extremalExpectation_apply (v k t : ℝ) (g : Polynomial ℝ) :
    extremalExpectation v k t g = ∫ x, g.eval x ∂extremalLaw v k t := rfl

theorem extremalExpectation_X_pow (v k t : ℝ) (n : ℕ) :
    extremalExpectation v k t (X^n) = ∫ x : ℝ, x^n ∂extremalLaw v k t := by
  change (∫ x, (X^n).eval x ∂extremalLaw v k t) = _
  simp only [eval_pow, eval_X]

theorem sharp_attained_bound (v k t : ℝ) (hv : 0 < v) (hd : 0 < delta v k) :
    ∃ E : Polynomial ℝ →ₗ[ℝ] ℝ,
      (∀ g : Polynomial ℝ, 0 ≤ E (g^2)) ∧
      E (X^0) = 1 ∧ E (X^1) = 0 ∧ E (X^2) = v ∧ E (X^3) = k ∧
        E (X^4) = 3*v^2 ∧ E (X^5) = t ∧ E (X^6) = floor v k t := by
  refine ⟨extremalExpectation v k t, ?_, ?_⟩
  · intro g
    change 0 ≤ ∫ x, (g^2).eval x ∂extremalLaw v k t
    apply integral_nonneg
    intro x
    simpa only [eval_pow, Pi.zero_apply] using sq_nonneg (g.eval x)
  · simpa only [extremalExpectation_X_pow] using extremalLaw_first_seven v k t hv hd

theorem extremal_boundary_square (v k t : ℝ) (hv : 0 < v) (hd : 0 < delta v k) :
    (∫ x, ((boundaryPolynomial v k t).eval x)^2 ∂extremalLaw v k t) = 0 := by
  have hm := extremalLaw_first_seven v k t hv hd
  simp only [← extremalExpectation_X_pow] at hm
  rcases hm with ⟨h0,h1,h2,h3,h4,h5,h6⟩
  have he := boundary_square_value (extremalExpectation v k t) v k t hd.ne'
    h0 h1 h2 h3 h4 h5
  rw [h6, sub_self] at he
  simpa only [extremalExpectation_apply, eval_pow] using he

theorem extremal_boundary_ae (v k t : ℝ) (hv : 0 < v) (hd : 0 < delta v k) :
    ∀ᵐ x ∂extremalLaw v k t, (boundaryPolynomial v k t).eval x = 0 := by
  have he := (integral_eq_zero_iff_of_nonneg
    (show 0 ≤ fun x => ((boundaryPolynomial v k t).eval x)^2 from fun x => sq_nonneg _)
    (extremalLaw_integrable v k t _)).mp (extremal_boundary_square v k t hv hd)
  filter_upwards [he] with x hx
  exact sq_eq_zero_iff.mp hx

theorem floor_one (t : ℝ) : floor 1 1 t = t^2-8*t+26 := by
  norm_num [floor,delta]
  ring

theorem mixed_sixth_gap (v k : ℝ) (hd : delta v k ≠ 0) :
    15*v^3+10*k^2-floor v k (10*v*k) =
      (12*v^6-24*v^3*k^2-9*k^4)/delta v k := by
  dsimp [floor]
  field_simp [hd]
  dsimp [delta]
  ring

end OperatorDerivativeRewrite.Foundation.RegularMixedMomentRealization
