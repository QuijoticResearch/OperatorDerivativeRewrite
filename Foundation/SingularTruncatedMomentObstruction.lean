import Foundation.MixedCubicThirdDegree
import Foundation.TruncatedPolynomialIntegration

/-! Cubic-square positivity of singular truncated data need not give a positive measure. -/
noncomputable section
open MeasureTheory Polynomial
namespace OperatorDerivativeRewrite.Foundation.SingularTruncatedMomentObstruction
open MixedCubicThirdDegree TruncatedPolynomialIntegration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def moment : ℕ → ℝ
  | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 12 | 5 => 32 | 6 => 89 | _ => 0

def expectation : Polynomial ℝ →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun n => moment n • LinearMap.id

theorem expectation_X_pow (n : ℕ) : expectation (X^n) = moment n := by
  have he : expectation (monomial n 1) = 1*moment n := by
    simp [expectation, Polynomial.lsum, smul_eq_mul, mul_comm]
  simpa only [monomial_one_right_eq_X_pow, one_mul] using he

def nullPolynomial : Polynomial ℝ := X^2-(2 : ℝ) • X^1-(2 : ℝ) • X^0

def basis (c b a d : ℝ) : Polynomial ℝ :=
  c • X^0+b • X^1+a • nullPolynomial+d • (X*nullPolynomial)

theorem basis_as_cubic (c b a d : ℝ) :
    basis c b a d = cubic (c-2*a) (b-2*a-2*d) (a-2*d) d := by
  simp only [basis, nullPolynomial, cubic, Algebra.smul_def, map_sub, map_mul,
    map_ofNat, pow_zero, pow_one]
  ring

theorem basis_natDegree (c b a d : ℝ) : (basis c b a d).natDegree ≤ 3 := by
  rw [basis_as_cubic]
  exact cubic_natDegree _ _ _ _

theorem cubic_as_basis (c b a d : ℝ) :
    cubic c b a d = basis (c+2*a+4*d) (b+2*a+6*d) (a+2*d) d := by
  rw [basis_as_cubic]
  simp only [cubic, Algebra.smul_def, map_sub, map_mul, map_add, map_ofNat]
  ring

theorem raw_cubic_square (c b a d : ℝ) :
    expectation ((cubic c b a d)^2) = c^2+2*(b^2+2*c*a)+
      4*(2*c*d+2*b*a)+12*(a^2+2*b*d)+64*a*d+89*d^2 := by
  have he : (cubic c b a d)^2 = c^2 • (X : Polynomial ℝ)^0+
      (2*c*b) • X^1+(b^2+2*c*a) • X^2+(2*c*d+2*b*a) • X^3+
      (a^2+2*b*d) • X^4+(2*a*d) • X^5+d^2 • X^6 := by
    simp only [cubic, Algebra.smul_def, map_add, map_mul, map_pow,
      map_ofNat, pow_zero, pow_one]
    ring
  rw [he]
  simp only [map_add, map_smul, expectation_X_pow, smul_eq_mul]
  norm_num [moment]
  ring

theorem basis_square (c b a d : ℝ) :
    expectation ((basis c b a d)^2) = c^2+2*b^2+d^2 := by
  rw [basis_as_cubic, raw_cubic_square]
  ring

theorem all_cubic_squares_nonneg (g : Polynomial ℝ) (hg : g.natDegree ≤ 3) :
    0 ≤ expectation (g^2) := by
  rw [cubic_of_natDegree g hg, cubic_as_basis, basis_square]
  positivity

theorem null_polynomial_basis : basis 0 0 1 0 = nullPolynomial := by simp [basis]
theorem shifted_null_basis : basis 0 0 0 1 = X*nullPolynomial := by simp [basis]

theorem null_square : expectation (nullPolynomial^2) = 0 := by
  rw [← null_polynomial_basis, basis_square]
  norm_num

theorem shifted_null_square : expectation ((X*nullPolynomial)^2) = 1 := by
  rw [← shifted_null_basis, basis_square]
  norm_num

theorem null_natDegree_le_two : nullPolynomial.natDegree ≤ 2 := by
  have he : nullPolynomial = MixedCubicMomentPositivity.quadratic (-2) (-2) 1 := by
    simp only [nullPolynomial, MixedCubicMomentPositivity.quadratic, Algebra.smul_def,
      map_neg, map_ofNat, map_one, pow_zero, pow_one]
    ring
  rw [he]
  exact MixedCubicMomentPositivity.quadratic_natDegree _ _ _

theorem multiplication_not_null_compatible :
    ∃ R : Polynomial ℝ, R.natDegree ≤ 2 ∧ expectation (R^2) = 0 ∧
      0 < expectation ((X*R)^2) := by
  exact ⟨nullPolynomial, null_natDegree_le_two, null_square, by rw [shifted_null_square]; norm_num⟩

theorem no_normed_coordinate_operator {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : Polynomial ℝ →ₗ[ℝ] H) (T : H →ₗ[ℝ] H)
    (henergy : ∀ g : Polynomial ℝ, g.natDegree ≤ 3 → ‖L g‖^2 = expectation (g^2))
    (hmul : ∀ g : Polynomial ℝ, g.natDegree ≤ 2 → L (X*g) = T (L g)) : False := by
  have hn := henergy nullPolynomial (null_natDegree_le_two.trans (by omega))
  rw [null_square] at hn
  have hL : L nullPolynomial = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  have hLX : L (X*nullPolynomial) = 0 := by
    rw [hmul _ null_natDegree_le_two, hL, map_zero]
  have hd : (X*nullPolynomial).natDegree ≤ 3 := by
    rw [← shifted_null_basis]
    exact basis_natDegree _ _ _ _
  have he := henergy _ hd
  rw [hLX, norm_zero, shifted_null_square] at he
  norm_num at he

theorem null_square_degree : (nullPolynomial^2).natDegree ≤ 6 := by
  have hd : nullPolynomial.natDegree ≤ 3 := by
    rw [← null_polynomial_basis]
    exact basis_natDegree _ _ _ _
  rw [natDegree_pow]
  omega

theorem shifted_null_square_degree : ((X*nullPolynomial)^2).natDegree ≤ 6 := by
  have hd : (X*nullPolynomial).natDegree ≤ 3 := by
    rw [← shifted_null_basis]
    exact basis_natDegree _ _ _ _
  rw [natDegree_pow]
  omega

theorem positive_null_annihilates (E : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ g : Polynomial ℝ, 0 ≤ E (g^2)) (R : Polynomial ℝ)
    (hR : E (R^2) = 0) (Q : Polynomial ℝ) : E (R*Q) = 0 := by
  by_contra hne
  let b := E (Q^2)
  let m := E (R*Q)
  let P := (b+1) • R-m • Q
  have hb : 0 ≤ b := hpos Q
  have hm : m ≠ 0 := hne
  have hp := hpos P
  have he : E (P^2) = -(b+2)*m^2 := by
    have hpoly : P^2 = (b+1)^2 • R^2-(2*(b+1)*m) • (R*Q)+m^2 • Q^2 := by
      dsimp only [P]
      simp only [Algebra.smul_def, map_add, map_mul, map_pow, map_ofNat]
      ring
    rw [hpoly]
    simp only [map_add, map_sub, map_smul, smul_eq_mul, hR]
    change (b+1)^2*0-2*(b+1)*m*m+m^2*b = -(b+2)*m^2
    ring
  have hn := mul_pos (show 0 < b+2 by linarith) (sq_pos_of_ne_zero hm)
  rw [he] at hp
  linarith

theorem positive_null_shift (E : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ g : Polynomial ℝ, 0 ≤ E (g^2)) (R : Polynomial ℝ)
    (hR : E (R^2) = 0) : E ((X*R)^2) = 0 := by
  have he := positive_null_annihilates E hpos R hR (X^2*R)
  have hp : R*(X^2*R) = (X*R)^2 := by ring
  rwa [hp] at he

theorem no_positive_polynomial_extension (E : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hm : ∀ n ≤ 6, E (X^n) = moment n) :
    ¬ ∀ g : Polynomial ℝ, 0 ≤ E (g^2) := by
  intro hpos
  have hpoly : nullPolynomial^2 = (X : Polynomial ℝ)^4-(4 : ℝ) • X^3+
      (8 : ℝ) • X^1+(4 : ℝ) • X^0 := by
    simp only [nullPolynomial, Algebra.smul_def, map_ofNat, pow_zero, pow_one]
    ring
  have hR : E (nullPolynomial^2) = 0 := by
    rw [hpoly]
    simp only [map_add, map_sub, map_smul, smul_eq_mul]
    rw [hm 4 (by omega), hm 3 (by omega), hm 1 (by omega), hm 0 (by omega)]
    norm_num [moment]
  have hshift : (X*nullPolynomial)^2 = (X : Polynomial ℝ)^6-(4 : ℝ) • X^5+
      (8 : ℝ) • X^3+(4 : ℝ) • X^2 := by
    simp only [nullPolynomial, Algebra.smul_def, map_ofNat, pow_zero, pow_one]
    ring
  have hXR : E ((X*nullPolynomial)^2) = 1 := by
    rw [hshift]
    simp only [map_add, map_sub, map_smul, smul_eq_mul]
    rw [hm 6 (by omega), hm 5 (by omega), hm 3 (by omega), hm 2 (by omega)]
    norm_num [moment]
  have he := positive_null_shift E hpos nullPolynomial hR
  rw [hXR] at he
  norm_num at he

theorem no_measure_truncated_realization (μ : Measure ℝ)
    (hi : ∀ n ≤ 6, Integrable (fun x : ℝ => x^n) μ) :
    ¬ ∀ n ≤ 6, (∫ x : ℝ, x^n ∂μ) = moment n := by
  intro hm
  have hmatch : ∀ n ≤ 6, (∫ x : ℝ, x^n ∂μ) = expectation (X^n) := by
    intro n hn
    rw [expectation_X_pow]
    exact hm n hn
  obtain ⟨hR, hRint⟩ := polynomial_integral_match μ expectation 6 hi hmatch
    (nullPolynomial^2) null_square_degree
  rw [null_square] at hRint
  have hae := (integral_eq_zero_iff_of_nonneg
    (show 0 ≤ fun x => (nullPolynomial^2).eval x from fun x => by
      simpa only [eval_pow, Pi.zero_apply] using sq_nonneg (nullPolynomial.eval x)) hR).mp hRint
  have hz : (fun x => ((X*nullPolynomial)^2).eval x) =ᵐ[μ] 0 := by
    filter_upwards [hae] with x hx
    have hroot : nullPolynomial.eval x = 0 := by
      apply sq_eq_zero_iff.mp
      simpa only [eval_pow, Pi.zero_apply] using hx
    simp only [eval_pow, eval_mul, eval_X, hroot, mul_zero, Pi.zero_apply]
    norm_num
  have hzero : (∫ x, ((X*nullPolynomial)^2).eval x ∂μ) = 0 := by
    rw [integral_congr_ae hz]
    simp
  have hone := (polynomial_integral_match μ expectation 6 hi hmatch
    ((X*nullPolynomial)^2) shifted_null_square_degree).2
  rw [shifted_null_square] at hone
  linarith

end OperatorDerivativeRewrite.Foundation.SingularTruncatedMomentObstruction
