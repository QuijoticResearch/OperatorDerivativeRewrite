import Foundation.FiniteGaussianIBP
import Mathlib.Tactic

/-! Exact fourth moments of arbitrary finite diagonal Gaussian quadratics,
derived by actual polynomial Gaussian integration by parts. -/
noncomputable section
open MeasureTheory MvPolynomial
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianDiagonalQuadraticMoments
open FiniteGaussian
variable {I : Type*} [Fintype I]

abbrev moment : MvPolynomial I ℝ →ₗ[ℝ] ℝ := productPolynomialIntegral

private theorem C_two : (C (2 : ℝ) : MvPolynomial I ℝ) = 2 := by
  convert C_eq_coe_nat (σ := I) (R := ℝ) 2 using 1

private theorem C_four : (C (4 : ℝ) : MvPolynomial I ℝ) = 4 := by
  convert C_eq_coe_nat (σ := I) (R := ℝ) 4 using 1

private theorem C_six : (C (6 : ℝ) : MvPolynomial I ℝ) = 6 := by
  convert C_eq_coe_nat (σ := I) (R := ℝ) 6 using 1

theorem stein (p : MvPolynomial I ℝ) (i : I) :
    moment (X i * p) = moment (pderiv i p) := by
  simpa only [productPolynomialIntegral, LinearMap.coe_mk, AddHom.coe_mk,
    map_mul, eval_X] using productPolynomial_stein p i

theorem centered_stein (p : MvPolynomial I ℝ) (i : I) :
    moment ((X i ^ 2 - 1) * p) = moment (X i * pderiv i p) := by
  classical
  have h := stein (X i * p) i
  have hl : X i * (X i * p) = X i^2 * p := by ring
  have hr : pderiv i (X i * p) = p + X i * pderiv i p := by simp [add_comm]
  rw [hl, hr, map_add] at h
  have he : (X i^2 - 1) * p = X i^2 * p - p := by ring
  rw [he, map_sub]
  linarith

theorem moment_one : moment (1 : MvPolynomial I ℝ) = 1 := by
  simp [productPolynomialIntegral]

theorem moment_coordinate_square (i : I) : moment (X i^2 : MvPolynomial I ℝ) = 1 := by
  classical
  have h := stein (X i) i
  simpa [← pow_two, moment_one] using h

def quadratic (a : I → ℝ) : MvPolynomial I ℝ := ∑ i, a i • (X i^2 - 1)

theorem quadratic_derivative (a : I → ℝ) (i : I) :
    pderiv i (quadratic a) = (2 * a i) • X i := by
  classical
  simp [quadratic, pderiv_X, Pi.single_apply, Algebra.smul_def, mul_ite, ite_mul]
  rw [C_two]
  ring

theorem quadratic_pairing (a : I → ℝ) (p : MvPolynomial I ℝ) :
    moment (quadratic a * p) = ∑ i, a i * moment (X i * pderiv i p) := by
  simp only [quadratic, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, smul_eq_mul]
  simp_rw [centered_stein]

theorem quadratic_centered (a : I → ℝ) : moment (quadratic a) = 0 := by
  have h := quadratic_pairing a 1
  simpa using h

theorem coordinate_square_quadratic (a : I → ℝ) (i : I) :
    moment (X i^2 * quadratic a) = 2 * a i := by
  have h := centered_stein (quadratic a) i
  have hl : (X i^2 - 1) * quadratic a = X i^2 * quadratic a - quadratic a := by ring
  have hr : X i * pderiv i (quadratic a) = (2 * a i) • X i^2 := by
    rw [quadratic_derivative]
    simp [Algebra.smul_def]
    ring
  rw [hl, map_sub, quadratic_centered, sub_zero, hr, map_smul,
    moment_coordinate_square, smul_eq_mul, mul_one] at h
  exact h

theorem quadratic_variance (a : I → ℝ) :
    moment (quadratic a ^ 2) = 2 * ∑ i, (a i)^2 := by
  rw [pow_two, quadratic_pairing]
  have ht (i : I) : moment (X i * pderiv i (quadratic a)) = 2 * a i := by
    rw [quadratic_derivative]
    have he : X i * ((2 * a i) • X i) = (2 * a i) • (X i^2 : MvPolynomial I ℝ) := by
      simp [Algebra.smul_def]
      ring
    rw [he, map_smul, moment_coordinate_square, smul_eq_mul, mul_one]
  simp_rw [ht]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem coordinate_square_quadratic_square (a : I → ℝ) (i : I) :
    moment (X i^2 * quadratic a^2) = 2 * ∑ j, (a j)^2 + 8 * (a i)^2 := by
  have h := centered_stein (quadratic a^2) i
  have hl : (X i^2 - 1) * quadratic a^2 = X i^2 * quadratic a^2 - quadratic a^2 := by ring
  have hr : X i * pderiv i (quadratic a^2) = (4 * a i) • (X i^2 * quadratic a) := by
    simp [quadratic_derivative, Algebra.smul_def]
    rw [C_two, C_four]
    ring
  rw [hl, map_sub, hr, map_smul, smul_eq_mul, coordinate_square_quadratic,
    quadratic_variance] at h
  nlinarith

theorem quadratic_fourth_moment (a : I → ℝ) :
    moment (quadratic a^4) = 12 * (∑ i, (a i)^2)^2 + 48 * ∑ i, (a i)^4 := by
  have he : quadratic a^4 = quadratic a * quadratic a^3 := by ring
  rw [he, quadratic_pairing]
  have ht (i : I) : a i * moment (X i * pderiv i (quadratic a^3)) =
      12 * (∑ j, (a j)^2) * (a i)^2 + 48 * (a i)^4 := by
    have hp : X i * pderiv i (quadratic a^3) = (6 * a i) • (X i^2 * quadratic a^2) := by
      simp [quadratic_derivative, Algebra.smul_def]
      rw [C_two, C_six]
      ring
    rw [hp, map_smul, smul_eq_mul, coordinate_square_quadratic_square]
    ring
  simp_rw [ht]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem sum_fourth_le_sum_square_sq (a : I → ℝ) :
    (∑ i, (a i)^4) ≤ (∑ i, (a i)^2)^2 := by
  classical
  have h (s : Finset I) : (∑ i ∈ s, (a i)^4) ≤ (∑ i ∈ s, (a i)^2)^2 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hp : 0 ≤ ∑ j ∈ s, (a j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
      nlinarith [sq_nonneg (a i)]
  exact h Finset.univ

theorem quadratic_fourth_upper_bound (a : I → ℝ) :
    moment (quadratic a^4) ≤ 15 * (moment (quadratic a^2))^2 := by
  rw [quadratic_fourth_moment, quadratic_variance]
  nlinarith [sum_fourth_le_sum_square_sq a]

theorem quadratic_fourth_lower_bound (a : I → ℝ) :
    3 * (moment (quadratic a^2))^2 ≤ moment (quadratic a^4) := by
  rw [quadratic_fourth_moment, quadratic_variance]
  have hp : 0 ≤ ∑ i, (a i)^4 := Finset.sum_nonneg (fun i _ => by positivity)
  nlinarith

theorem flat_variance :
    moment (quadratic (fun _ : I => (1 : ℝ))^2) = 2 * (Fintype.card I : ℝ) := by
  rw [quadratic_variance]
  simp

theorem flat_fourth_moment :
    moment (quadratic (fun _ : I => (1 : ℝ))^4) =
      12 * (Fintype.card I : ℝ)^2 + 48 * (Fintype.card I : ℝ) := by
  rw [quadratic_fourth_moment]
  simp

theorem flat_fourth_ratio (hI : 0 < Fintype.card I) :
    moment (quadratic (fun _ : I => (1 : ℝ))^4) /
      (moment (quadratic (fun _ : I => (1 : ℝ))^2))^2 =
        3 + 12/(Fintype.card I : ℝ) := by
  rw [flat_fourth_moment, flat_variance]
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  field_simp
  ring

end OperatorDerivativeRewrite.Foundation.GaussianDiagonalQuadraticMoments
