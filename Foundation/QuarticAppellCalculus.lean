import Foundation.BiharmonicFiniteRecovery

/-! Polynomial raising and integration by parts for the actual quartic signed law. -/
noncomputable section
open Polynomial
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.QuarticAppellCalculus
open PseudoPolynomialStein PseudoClarkOconeObstruction

def raise (a : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  X * P - (4*a) • derivative^[3] P

theorem raise_mean_zero (a : ℝ) (P : Polynomial ℝ) :
    expectation 4 a (raise a P) = 0 := by
  rw [raise, map_sub, map_smul, polynomial_stein]
  simp only [smul_eq_mul]
  norm_num

theorem derivative_raise (a : ℝ) (P : Polynomial ℝ) :
    derivative (raise a P) = P + raise a (derivative P) := by
  simp only [raise, map_sub, derivative_mul, derivative_X, one_mul,
    derivative_smul, Function.iterate_succ_apply, Function.iterate_zero_apply]
  ring

theorem raise_smul (a c : ℝ) (P : Polynomial ℝ) :
    raise a (c • P) = c • raise a P := by
  simp only [raise, mul_smul_comm, iterate_derivative_smul, smul_sub, smul_smul]
  rw [mul_comm (4*a) c]

def appell (a : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | n+1 => raise a (appell a n)

theorem appell_mean_zero (a : ℝ) (n : ℕ) :
    expectation 4 a (appell a (n+1)) = 0 := raise_mean_zero a _

theorem appell_derivative (a : ℝ) (n : ℕ) :
    derivative (appell a (n+1)) = (n+1 : ℝ) • appell a n := by
  induction n with
  | zero => simp [appell, raise]
  | succ n ih =>
    change derivative (raise a (appell a (n+1))) = _
    rw [derivative_raise, ih, raise_smul]
    change appell a (n+1) + (n+1 : ℝ) • appell a (n+1) = _
    push_cast
    module

theorem raise_pairing (a : ℝ) (P Q : Polynomial ℝ) :
    pairing 4 a (raise a P) Q = (4*a) *
      (3 * pairing 4 a (derivative (derivative P)) (derivative Q) +
       3 * pairing 4 a (derivative P) (derivative (derivative Q)) +
       pairing 4 a P (derivative (derivative (derivative Q)))) := by
  have hd : derivative^[3] (P*Q) = derivative^[3] P * Q +
      (3 : ℝ) • (derivative (derivative P) * derivative Q) +
      (3 : ℝ) • (derivative P * derivative (derivative Q)) +
      P * derivative (derivative (derivative Q)) := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply,
      derivative_mul, map_add]
    module
  unfold pairing raise
  rw [sub_mul, smul_mul_assoc, map_sub, map_smul, mul_assoc,
    polynomial_stein, hd, map_add, map_add, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

theorem actual_raise_mean_zero (t : ℝ≥0) (ht : 0 < t) (P : Polynomial ℝ) :
    HigherHeatPolynomialRealization.kernelExpectation 2 (by norm_num) t ht
      (raise (-(t:ℝ)) P) = 0 := by
  rw [HigherHeatPolynomialRealization.kernelExpectation_eq_moments]
  norm_num
  exact raise_mean_zero _ _

theorem appell_fifth (a : ℝ) : appell a 5 = BiharmonicFiniteRecovery.fifthProbe a := by
  norm_num [appell, raise, Function.iterate_succ_apply, Function.iterate_zero_apply,
    derivative_mul, derivative_pow, BiharmonicFiniteRecovery.fifthProbe]
  simp only [smul_eq_C_mul, map_mul, map_ofNat]
  ring

theorem actual_raise_pairing (t : ℝ≥0) (ht : 0 < t) (P Q : Polynomial ℝ) :
    HigherHeatPolynomialRealization.kernelExpectation 2 (by norm_num) t ht
      (raise (-(t:ℝ)) P * Q) = (-4*(t:ℝ)) *
      (3 * HigherHeatPolynomialRealization.kernelExpectation 2 (by norm_num) t ht
        (derivative (derivative P) * derivative Q) +
       3 * HigherHeatPolynomialRealization.kernelExpectation 2 (by norm_num) t ht
        (derivative P * derivative (derivative Q)) +
       HigherHeatPolynomialRealization.kernelExpectation 2 (by norm_num) t ht
        (P * derivative (derivative (derivative Q)))) := by
  simp only [HigherHeatPolynomialRealization.kernelExpectation_eq_moments]
  convert raise_pairing (-(t:ℝ)) P Q using 1 <;> norm_num [pairing]

theorem appell_fifth_finite_dual_leakage (a : ℝ) (ha : a ≠ 0) :
    pairing 4 a (appell a 5) (BiharmonicFiniteRecovery.dual a 1) = 720*a := by
  rw [appell_fifth]
  exact BiharmonicFiniteRecovery.finite_dual_leakage a ha

end OperatorDerivativeRewrite.Foundation.QuarticAppellCalculus
