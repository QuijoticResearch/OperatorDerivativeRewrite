import Foundation.FourierPathDirectionalOperator
import Foundation.HigherHeatFourierPathDerivative

/-! A genuine continuous rough direction and an explicit dyadic quartic probe family. -/
noncomputable section
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathRoughDirection
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathDirectionalCharacters

def rootEight (t : ℝ) : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (max t 0)))

theorem rootEight_continuous : Continuous rootEight := by unfold rootEight; fun_prop

theorem rootEight_pow (x : ℝ) (hx : 0 ≤ x) : rootEight (x^8)=x := by
  unfold rootEight
  rw [max_eq_left (pow_nonneg hx _)]
  have h8 : x^8=(x^4)^2 := by ring
  have h4 : x^4=(x^2)^2 := by ring
  rw [h8, Real.sqrt_sq (pow_nonneg hx _), h4, Real.sqrt_sq (sq_nonneg x), Real.sqrt_sq hx]

def direction : Path := ⟨⟨rootEight,rootEight_continuous⟩, by simp [rootEight]⟩

def levels (n : ℕ) : ℕ := 8*n

def first (n : ℕ) : Fin (gridSize (levels n)) := ⟨0,gridSize_pos _⟩

def small (n : ℕ) : ℝ := ((2:ℝ)^n)⁻¹

theorem small_nonneg (n : ℕ) : 0 ≤ small n := by unfold small; positivity

theorem first_time (n : ℕ) : sampleTime (levels n) (first n)=(small n)^8 := by
  change (((first n).val+1:ℕ):ℝ)*(duration 1 (levels n):ℝ)=_
  simp only [first, Nat.zero_add, Nat.cast_one, one_mul]
  change (1:ℝ)/(gridSize (levels n):ℝ)=(small n)^8
  rw [gridSize_pow, Nat.cast_pow, Nat.cast_ofNat, one_div, small, inv_pow, ← pow_mul]
  congr 2
  unfold levels
  omega

theorem sample_direction_first (n : ℕ) : sample (levels n) direction (first n)=small n := by
  change rootEight (sampleTime (levels n) (first n))=small n
  rw [first_time, rootEight_pow _ (small_nonneg n)]

def amplitude (n : ℕ) : ℝ := (2:ℝ)^(2*n)/(2*Real.pi)

def frequencies (n : ℕ) : Grid (levels n) := fun j => if j=first n then amplitude n else 0

theorem backward_sum (n : ℕ) (j : Fin (gridSize (levels n))) :
    (∑ k ∈ Finset.univ.filter (fun k => j ≤ k), frequencies n k)=
      if j=first n then amplitude n else 0 := by
  classical
  by_cases hj : j=first n
  · subst j
    rw [if_pos rfl, Finset.sum_eq_single (first n)]
    · simp [frequencies]
    · intro k hk hki
      simp [frequencies, hki]
    · simp
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k ≠ first n := by
      intro he
      have hv : j.val ≤ 0 := by
        have hv := (Finset.mem_filter.mp hk).2
        rw [he] at hv
        exact hv
      apply hj
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero hv
    simp [frequencies, hkn]

theorem normalized_amplitude (n : ℕ) : 2*Real.pi*amplitude n=(2:ℝ)^(2*n) := by
  unfold amplitude
  have hp : 2*Real.pi ≠ 0 := by positivity
  exact mul_div_cancel₀ _ hp

theorem scalar_cancel (n : ℕ) : (2:ℝ)^(2*n)*small n=(2:ℝ)^n := by
  unfold small
  have he : 2*n=n+n := by omega
  rw [he, pow_add, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]

theorem directional_frequency (n : ℕ) :
    frequency levels frequencies direction (n+1)=-(2:ℝ)^n := by
  classical
  change 2*Real.pi * (-(∑ j, frequencies n j * sample (levels n) direction j))=_
  have he : (∑ j, frequencies n j * sample (levels n) direction j)=
      amplitude n*sample (levels n) direction (first n) := by
    rw [Finset.sum_eq_single (first n)]
    · simp [frequencies]
    · intro j hj hji
      simp [frequencies, hji]
    · simp
  rw [he, sample_direction_first]
  calc
    _ = -(2*Real.pi*amplitude n*small n) := by ring
    _ = _ := by rw [normalized_amplitude, scalar_cancel]

theorem quartic_rate (n : ℕ) :
    HigherHeatFourierPathDerivative.rate levels frequencies 2 (n+1)=1 := by
  classical
  change (∑ j : Fin (gridSize (levels n)), HigherHeatGenerator.weight 2
    (∑ k ∈ Finset.univ.filter (fun k => j ≤ k), frequencies n k)) /
      (gridSize (levels n):ℝ)=1
  have he (j : Fin (gridSize (levels n))) : HigherHeatGenerator.weight 2
      (∑ k ∈ Finset.univ.filter (fun k => j ≤ k), frequencies n k)=
      if j=first n then ((2:ℝ)^(2*n))^4 else 0 := by
    rw [backward_sum]
    by_cases hj : j=first n
    · rw [if_pos hj, if_pos hj]
      unfold HigherHeatGenerator.weight
      rw [normalized_amplitude]
    · simp [hj, HigherHeatGenerator.weight]
  simp_rw [he]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [gridSize_pow, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  have hp : (2*n)*4=levels n := by unfold levels; omega
  rw [hp, div_self (by positivity)]

end OperatorDerivativeRewrite.Foundation.FourierPathRoughDirection
