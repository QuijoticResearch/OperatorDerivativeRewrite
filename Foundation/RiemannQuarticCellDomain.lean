import Foundation.RiemannQuarticPhaseJets
import Foundation.RiemannQuarticIntervalChecks

/-! Actual range-reduction domains for the finite arithmetic quadrature. -/
open Set
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCellDomain
open RiemannQuarticPhaseJets RiemannQuarticIntervalChecks

theorem exp_four_bound (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (8/5)) :
    Real.exp (4*u) ≤ 603 := by
  calc
    _ ≤ Real.exp (32/5 : ℝ) := Real.exp_le_exp.mpr (by linarith [hu.2])
    _ ≤ (601845039/10^6 : ℝ) := exp32fifths_bounds.2
    _ ≤ _ := by norm_num

theorem phase_bounds (m : ℕ) (hm : m ≤ 4) (a u : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 9) (hu : u ∈ Icc (0 : ℝ) (8/5)) :
    (-40000 : ℝ) ≤ phase m a u ∧ phase m a u ≤ 100 := by
  have hm' : (m : ℝ) ≤ 4 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm2 : (m : ℝ)^2 ≤ 16 := by nlinarith
  have hp : Real.pi*(m : ℝ)^2 ≤ 64 := by
    have hh := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (sq_nonneg (m : ℝ))
    nlinarith
  have htheta : Real.pi*(m : ℝ)^2*Real.exp (4*u) ≤ (38592 : ℝ) := by
    calc
      _ ≤ 64*603 := mul_le_mul hp (exp_four_bound u hu) (Real.exp_pos _).le (by norm_num)
      _ = _ := by norm_num
  have ht0 : 0 ≤ Real.pi*(m : ℝ)^2*Real.exp (4*u) := by positivity
  have hu4 := pow_le_pow_left₀ hu.1 hu.2 4
  have hau : a*u ≤ (9 : ℝ)*(8/5) := mul_le_mul ha.2 hu.2 hu.1 (by norm_num)
  have hau0 := mul_nonneg ha.1 hu.1
  unfold phase
  simp only [pow_one]
  constructor <;> nlinarith [pow_nonneg hu.1 4]

theorem phase_scaled_small (m : ℕ) (hm : m ≤ 4) (a u : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 9) (hu : u ∈ Icc (0 : ℝ) (8/5)) :
    |phase m a u/((2^16 : ℕ) : ℝ)| ≤ 1 := by
  have h := phase_bounds m hm a u ha hu
  rw [abs_le]
  norm_num
  constructor <;> linarith

theorem four_scaled_small (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (8/5)) :
    |4*u/((2^4 : ℕ) : ℝ)| ≤ 1 := by
  rw [abs_le]
  norm_num
  constructor <;> linarith [hu.1, hu.2]

theorem frequency_scaled_small (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (8/5)) :
    |((632083/10000 : ℝ)*u)/((2^8 : ℕ) : ℝ)| ≤ 1 := by
  rw [abs_le]
  norm_num
  constructor <;> linarith [hu.1, hu.2]

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCellDomain
