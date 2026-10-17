import Foundation.FourierPathDirectionalCharacters
import Foundation.HigherHeatFourierPathDerivative
import Mathlib.Order.Interval.Finset.Fin

/-! Uniform spectral control of the genuine linear path direction on all dyadic levels. -/
noncomputable section
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathLinearDirection
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathDirectionalCharacters HigherHeatFourierPathDerivative

def direction : Path := ⟨ContinuousMap.id ℝ,rfl⟩

theorem sample_direction (n : ℕ) (j : Fin (gridSize n)) :
    sample n direction j=(j.val+1:ℝ)/(gridSize n:ℝ) := by
  change (HigherHeatDyadicLaws.time 1 n j:ℝ)=_
  change ((j.val+1:ℕ):ℝ)*((1:ℝ)/(gridSize n:ℝ))=_
  push_cast
  ring

theorem sum_backward (N : ℕ) (x : Fin N → ℝ) :
    (∑ j, ∑ k ∈ Finset.univ.filter (fun k => j ≤ k), x k)=
      ∑ k, (k.val+1:ℝ)*x k := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun j : Fin N => j ≤ k)=Finset.Iic k := by ext j; simp
  rw [he, Finset.sum_const, Fin.card_Iic]
  simp [nsmul_eq_mul]

theorem abs_le_one_add_even (m : ℕ) (hm : 0 < m) (x : ℝ) : |x| ≤ 1+x^(2*m) := by
  by_cases hx : |x| ≤ 1
  · have hp : 0 ≤ x^(2*m) := by rw [pow_mul]; positivity
    linarith
  · have hp := le_self_pow₀ (le_of_not_ge hx) (show 2*m ≠ 0 by omega)
    rw [pow_abs_two_mul] at hp
    linarith

theorem average_bound (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N) (x : Fin N → ℝ) :
    |(∑ j, x j)/(N:ℝ)| ≤ 1+(∑ j, (x j)^(2*m))/(N:ℝ) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  rw [abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    |∑ j, x j| ≤ ∑ j, |x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (1+(x j)^(2*m)) := Finset.sum_le_sum (fun j hj => abs_le_one_add_even m hm _)
    _ = (1+(∑ j, (x j)^(2*m))/(N:ℝ))*(N:ℝ) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      field_simp

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem frequency_average (i : ℕ) : frequency levels ξ direction i=
    -((∑ j : Fin (gridSize (spectrumLevels levels i)), 2*Real.pi*
      (∑ k ∈ Finset.univ.filter (fun k => j ≤ k), spectrumFrequency levels ξ i k)) /
        (gridSize (spectrumLevels levels i):ℝ)) := by
  unfold frequency
  simp_rw [sample_direction, ← mul_div_assoc]
  rw [← Finset.sum_div]
  have he : (∑ j : Fin (gridSize (spectrumLevels levels i)), 2*Real.pi*
      (∑ k ∈ Finset.univ.filter (fun k => j ≤ k), spectrumFrequency levels ξ i k))=
      2*Real.pi*(∑ k, spectrumFrequency levels ξ i k*(k.val+1:ℝ)) := by
    rw [← Finset.mul_sum, sum_backward]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he]
  ring

theorem frequency_bound (m : ℕ) (hm : 0 < m) (i : ℕ) :
    |frequency levels ξ direction i| ≤ 1+rate levels ξ m i := by
  rw [frequency_average, abs_neg]
  exact average_bound m hm _ (gridSize_pos _) _

theorem damped_rate_bound (T r : ℝ) (hT : 0 < T) (hr : 0 ≤ r) :
    (1+r)*Real.exp (-T*r) ≤ 1+T⁻¹ := by
  have he : Real.exp (-T*r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hb : r*Real.exp (-T*r) ≤ T⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hT).mpr
    have hh := (Real.mul_exp_neg_le_exp_neg_one (T*r)).trans
      (Real.exp_le_one_iff.mpr (by norm_num : -(1:ℝ) ≤ 0))
    have heq : -(T*r) = -T*r := by ring
    rw [heq] at hh
    convert hh using 1 <;> ring
  nlinarith

theorem damped_frequency_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖eigenvalue (frequency levels ξ direction i)*
      HigherHeatFourierPathSemigroup.multiplier levels ξ m T i‖ ≤ 1+(T:ℝ)⁻¹ := by
  rw [norm_mul, eigenvalue_norm, multiplier_exp, Complex.norm_real]
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_right (frequency_bound levels ξ m hm i)
    (Real.exp_pos _).le).trans (damped_rate_bound _ _ (by exact_mod_cast hT)
      (rate_nonneg levels ξ m i))

end OperatorDerivativeRewrite.Foundation.FourierPathLinearDirection
