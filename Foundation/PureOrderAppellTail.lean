import Foundation.PureOrderAppellExpansion
import Foundation.QuarticAppellExpansion

/-! Exact finite Appell tails and the missing lower-degree reconstruction terms.
No chronological stochastic integral or convergence is defined by this algebra. -/
noncomputable section
open Polynomial
namespace OperatorDerivativeRewrite.Foundation.PureOrderAppellTail
open PureOrderAppellCalculus PureOrderAppellExpansion PseudoPolynomialStein

theorem quartic_compatibility (a : ℝ) (n : ℕ) :
    appell 4 a n = QuarticAppellCalculus.appell a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [appell, raise, QuarticAppellCalculus.appell,
      QuarticAppellCalculus.raise, ih, Nat.cast_ofNat]

def lowPart (p : ℕ) (a : ℝ) (r : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  ∑ n ∈ Finset.range r, coordinate p a n P • appell p a n

def tailPart (p : ℕ) (a : ℝ) (r : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  P - lowPart p a r P

theorem coordinate_lowPart (p : ℕ) (a : ℝ) (r n : ℕ) (P : Polynomial ℝ) :
    coordinate p a n (lowPart p a r P) = if n < r then coordinate p a n P else 0 := by
  simp [lowPart, map_sum, map_smul, coordinate_appell, smul_eq_mul]

theorem coordinate_tailPart (p : ℕ) (a : ℝ) (r n : ℕ) (P : Polynomial ℝ) :
    coordinate p a n (tailPart p a r P) = if n < r then 0 else coordinate p a n P := by
  rw [tailPart, map_sub, coordinate_lowPart]
  split_ifs <;> simp

theorem coordinate_ext (p : ℕ) (a : ℝ) (P Q : Polynomial ℝ)
    (h : ∀ n, coordinate p a n P = coordinate p a n Q) : P = Q := by
  apply (basis p a).repr.injective
  ext n
  change (basis p a).repr P n = (basis p a).repr Q n
  simpa only [← Module.Basis.coord_apply, ← coordinate_eq_basis_coord] using h n

theorem lowPart_derivative_zero (p : ℕ) (a : ℝ) (r : ℕ) (P : Polynomial ℝ) :
    derivative^[r] (lowPart p a r P) = 0 := by
  rw [← Module.End.pow_apply]
  rw [lowPart, map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  rw [map_smul, Module.End.pow_apply]
  have hz : derivative^[r] (appell p a n) = 0 :=
    iterate_derivative_eq_zero (by
      rw [(appell_monic_degree p a n).natDegree_eq]
      exact Finset.mem_range.mp hn)
  rw [hz, smul_zero]

theorem tailPart_derivative (p : ℕ) (a : ℝ) (r : ℕ) (P : Polynomial ℝ) :
    derivative^[r] (tailPart p a r P) = derivative^[r] P := by
  rw [← Module.End.pow_apply]
  rw [tailPart, map_sub, Module.End.pow_apply, Module.End.pow_apply,
    lowPart_derivative_zero, sub_zero]

theorem coordinate_constant (p : ℕ) (a c : ℝ) (n : ℕ) :
    coordinate p a n (C c) = if n=0 then c else 0 := by
  have he : (C c : Polynomial ℝ) = c • appell p a 0 := by simp [appell, smul_eq_C_mul]
  rw [he, map_smul, coordinate_appell]
  by_cases hn : n=0
  · subst n; simp
  · simp [hn, Ne.symm hn]

theorem coordinate_zero (p : ℕ) (a : ℝ) (P : Polynomial ℝ) :
    coordinate p a 0 P = expectation p a P := by simp [coordinate_apply]

theorem tail_eq_centered_iff (p : ℕ) (a : ℝ) (r : ℕ) (hr : 0 < r) (P : Polynomial ℝ) :
    tailPart p a r P = P-C (expectation p a P) ↔
      ∀ n, 0 < n → n < r → coordinate p a n P = 0 := by
  constructor
  · intro h n hn hnr
    have he := congrArg (coordinate p a n) h
    rw [coordinate_tailPart, ite_eq_left hnr, map_sub, coordinate_constant,
      ite_eq_right (ne_of_gt hn), sub_zero] at he
    exact he.symm
  · intro h
    apply coordinate_ext p a
    intro n
    rw [coordinate_tailPart, map_sub, coordinate_constant]
    by_cases hn : n=0
    · subst n
      simp [hr, coordinate_zero]
    · by_cases hnr : n<r
      · simp [hn, hnr, h n (by omega) hnr]
      · simp [hn, hnr]

theorem actual_coordinate (m : ℕ) (hm : 0 < m) (t : NNReal) (ht : 0 < t)
    (P : Polynomial ℝ) (n : ℕ) :
    coordinate (2*m) ((-1:ℝ)^(m+1)*(t:ℝ)) n P =
      HigherHeatPolynomialRealization.kernelExpectation m hm t ht (derivative^[n] P) /
        (n.factorial:ℝ) := by
  rw [coordinate_apply, HigherHeatPolynomialRealization.kernelExpectation_eq_moments]


theorem multiple_power_low_coordinates (p : ℕ) (hp : 0 < p) (a : ℝ) (k : ℕ)
    (hk : 0 < k) (n : ℕ) (hn : 0 < n) (hnp : n < p) :
    coordinate p a n (X^(p*k)) = 0 := by
  have hle : n ≤ p*k := (Nat.le_of_lt hnp).trans (Nat.le_mul_of_pos_right p hk)
  have hnot : ¬ p ∣ p*k-n := by
    intro hd
    have hh := Nat.dvd_sub (dvd_mul_right p k) hd
    have he : p*k-(p*k-n)=n := by omega
    rw [he] at hh
    have := Nat.le_of_dvd hn hh
    omega
  rw [coordinate_apply, iterate_derivative_X_pow_eq_smul, map_smul,
    expectation_X_pow, moment_off_order p hp a _ hnot]
  simp

theorem multiple_power_tail (p : ℕ) (hp : 0 < p) (a : ℝ) (k : ℕ) (hk : 0 < k) :
    tailPart p a p (X^(p*k)) = X^(p*k)-C (expectation p a (X^(p*k))) := by
  apply (tail_eq_centered_iff p a p hp _).mpr
  exact fun n hn hnp => multiple_power_low_coordinates p hp a k hk n hn hnp

theorem next_power_first_coordinate (p : ℕ) (hp : 0 < p) (a : ℝ) :
    coordinate p a 1 (X^(p+1)) = (p+1:ℝ)*(p.factorial:ℝ)*a := by
  rw [coordinate_apply, iterate_derivative_X_pow_eq_smul, map_smul,
    expectation_X_pow]
  simp only [Nat.add_sub_cancel, Nat.descFactorial_one, Nat.cast_add, Nat.cast_one,
    Nat.factorial_one, div_one, smul_eq_mul, moment_leading p hp]
  ring

theorem next_power_tail_not_centered (p : ℕ) (hp : 1 < p) (a : ℝ) (ha : a ≠ 0) :
    tailPart p a p (X^(p+1)) ≠ X^(p+1)-C (expectation p a (X^(p+1))) := by
  intro h
  have hh := (tail_eq_centered_iff p a p (by omega) _).mp h 1 (by omega) hp
  rw [next_power_first_coordinate p (by omega)] at hh
  exact mul_ne_zero (mul_ne_zero (by positivity)
    (by exact_mod_cast Nat.factorial_ne_zero p)) ha hh

end OperatorDerivativeRewrite.Foundation.PureOrderAppellTail
