import Foundation.FourierPathDyadicDirections

/-! Uniform higher-heat directional damping for every locally Lipschitz path direction. -/
noncomputable section
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathLipschitzDamping
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatCylinderFourier HigherHeatFourierPathDerivative FourierPathDirectionalCharacters
open FourierPathDyadicDirections

theorem average_abs_bound (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N) (x : Fin N → ℝ) :
    (∑ j, |x j|)/(N:ℝ) ≤ 1+(∑ j, (x j)^(2*m))/(N:ℝ) := by
  have hh := FourierPathLinearDirection.average_bound m hm N hN (fun j => |x j|)
  have hn : 0 ≤ (∑ j, |x j|)/(N:ℝ) := by positivity
  simpa only [abs_of_nonneg hn, pow_abs_two_mul] using hh

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem frequency_increment (h : Path) (i : ℕ) : frequency levels ξ h i=
    -(∑ j : Fin (gridSize (spectrumLevels levels i)),
      (2*Real.pi*(∑ k ∈ Finset.univ.filter (fun k => j ≤ k), spectrumFrequency levels ξ i k))*
        increment h (gridSize (spectrumLevels levels i)) j) := by
  unfold frequency
  rw [sample_cumulative, dot_linearImage]
  simp_rw [cumulative_dual]
  have he : (∑ j : Fin (gridSize (spectrumLevels levels i)),
      (2*Real.pi*(∑ k ∈ Finset.univ.filter (fun k => j ≤ k), spectrumFrequency levels ξ i k))*
        increment h (gridSize (spectrumLevels levels i)) j)=
      2*Real.pi*(∑ j : Fin (gridSize (spectrumLevels levels i)),
        increment h (gridSize (spectrumLevels levels i)) j*
          (∑ k ∈ Finset.univ.filter (fun k => j ≤ k), spectrumFrequency levels ξ i k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  ring

theorem frequency_bound (h : Path) (K : ℝ≥0)
    (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1)) (m : ℕ) (hm : 0 < m) (i : ℕ) :
    |frequency levels ξ h i| ≤ (K:ℝ)*(1+rate levels ξ m i) := by
  let N := gridSize (spectrumLevels levels i)
  let x : Fin N → ℝ := fun j => 2*Real.pi*
    (∑ k ∈ Finset.univ.filter (fun k => j ≤ k), spectrumFrequency levels ξ i k)
  rw [frequency_increment, abs_neg]
  change |∑ j, x j*increment h N j| ≤ _
  calc
    |∑ j, x j*increment h N j| ≤ ∑ j, |x j*increment h N j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |x j| *|increment h N j| := by simp only [abs_mul]
    _ ≤ ∑ j, |x j| *((K:ℝ)/(N:ℝ)) := Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (increment_bound h K hK N (gridSize_pos _) j) (abs_nonneg _))
    _ = (K:ℝ)*((∑ j, |x j|)/(N:ℝ)) := by rw [← Finset.sum_mul]; ring
    _ ≤ (K:ℝ)*(1+rate levels ξ m i) :=
      mul_le_mul_of_nonneg_left (average_abs_bound m hm N (gridSize_pos _) x) K.coe_nonneg

def bound (K : ℝ≥0) (T : ℝ≥0) : ℝ := (1+(K:ℝ))*(1+(T:ℝ)⁻¹)

theorem bound_pos (K : ℝ≥0) (T : ℝ≥0) : 0 < bound K T := by unfold bound; positivity

theorem damped_frequency_bound (h : Path) (K : ℝ≥0)
    (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1))
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖eigenvalue (frequency levels ξ h i)*
      HigherHeatFourierPathSemigroup.multiplier levels ξ m T i‖ ≤ bound K T := by
  rw [norm_mul, eigenvalue_norm, multiplier_exp, Complex.norm_real]
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ ((K:ℝ)*(1+rate levels ξ m i))*Real.exp (-(T:ℝ)*rate levels ξ m i) :=
      mul_le_mul_of_nonneg_right (frequency_bound levels ξ h K hK m hm i) (Real.exp_pos _).le
    _ = (K:ℝ)*((1+rate levels ξ m i)*Real.exp (-(T:ℝ)*rate levels ξ m i)) := by ring
    _ ≤ (K:ℝ)*(1+(T:ℝ)⁻¹) := mul_le_mul_of_nonneg_left
      (FourierPathLinearDirection.damped_rate_bound _ _ (by exact_mod_cast hT)
        (rate_nonneg levels ξ m i)) K.coe_nonneg
    _ ≤ bound K T := by unfold bound; gcongr; linarith

end OperatorDerivativeRewrite.Foundation.FourierPathLipschitzDamping
