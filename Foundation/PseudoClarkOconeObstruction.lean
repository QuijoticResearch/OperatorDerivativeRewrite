import Foundation.PseudoPolynomialStein

/-! A p-th derivative cannot recover every centered polynomial, even for an indefinite pairing. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PseudoClarkOconeObstruction
open Polynomial PseudoPolynomialStein

def pairing (p : ℕ) (a : ℝ) (P Q : Polynomial ℝ) : ℝ := expectation p a (P*Q)

def centered (p : ℕ) (a : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  P-C (expectation p a P)

theorem linear_mean_zero (p : ℕ) (hp : 1 < p) (a : ℝ) : expectation p a X=0 := by
  rw [← pow_one (X : Polynomial ℝ),expectation_X_pow]
  apply moment_off_order p (by omega) a 1
  intro hd
  have h := Nat.le_of_dvd (by norm_num : 0 < (1:ℕ)) hd
  omega

theorem centered_linear (p : ℕ) (hp : 1 < p) (a : ℝ) : centered p a X=X := by
  simp [centered,linear_mean_zero p hp a]

theorem linear_pairing (p : ℕ) (hp : 0 < p) (a : ℝ) :
    pairing p a X (X^(p-1))=(p.factorial:ℝ)*a := by
  rw [pairing,← pow_succ']
  have he : p-1+1=p := by omega
  rw [he,expectation_X_pow,moment_leading p hp]

theorem linear_not_radical (p : ℕ) (hp : 0 < p) (a : ℝ) (ha : a ≠ 0) :
    pairing p a X (X^(p-1)) ≠ 0 := by
  rw [linear_pairing p hp]
  exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero p) ha

theorem linear_square_zero (p : ℕ) (hp : 2 < p) (a : ℝ) : pairing p a X X=0 := by
  rw [pairing,← pow_two,expectation_X_pow]
  apply moment_off_order p (by omega) a 2
  intro hd
  have h := Nat.le_of_dvd (by norm_num : 0 < (2:ℕ)) hd
  omega

theorem zero_square_does_not_mean_radical (p : ℕ) (hp : 2 < p) (a : ℝ) (ha : a ≠ 0) :
    pairing p a X X=0 ∧ ∃ Q : Polynomial ℝ, pairing p a X Q ≠ 0 :=
  ⟨linear_square_zero p hp a, X^(p-1),linear_not_radical p (by omega) a ha⟩

def pDerivative (p : ℕ) : Module.End ℝ (Polynomial ℝ) := Polynomial.derivative^p

theorem pDerivative_linear_zero (p : ℕ) (hp : 1 < p) : pDerivative p X=0 := by
  rw [pDerivative,Module.End.pow_apply]
  exact iterate_derivative_X hp

theorem no_reconstruction_annihilating_linear {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : ℕ) (hp : 1 < p) (a : ℝ) (ha : a ≠ 0)
    (D : Polynomial ℝ →ₗ[ℝ] V) (hD : D X=0) (R : V →ₗ[ℝ] Polynomial ℝ) :
    ¬ ∀ P Q : Polynomial ℝ, pairing p a (centered p a P-R (D P)) Q=0 := by
  intro h
  have hh := h X (X^(p-1))
  rw [centered_linear p hp a,hD,map_zero,sub_zero] at hh
  exact linear_not_radical p (by omega) a ha hh

theorem pth_derivative_reconstruction_impossible (p : ℕ) (hp : 1 < p) (a : ℝ) (ha : a ≠ 0)
    (R : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ) :
    ¬ ∀ P Q : Polynomial ℝ, pairing p a (centered p a P-R (pDerivative p P)) Q=0 :=
  no_reconstruction_annihilating_linear p hp a ha (pDerivative p) (pDerivative_linear_zero p hp) R

end OperatorDerivativeRewrite.Foundation.PseudoClarkOconeObstruction
