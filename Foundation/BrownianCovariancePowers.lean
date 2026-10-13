import Foundation.FractionalCovarianceMatrices

/-! Exact finite Brownian-point innovation factorization. Natural matrix powers
are never confused with entrywise powers. Adjacent-level comparisons use ratios
of innovation variances. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset
namespace OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers

def innovation (k j : ℕ) : ℝ := ((j+1:ℕ):ℝ)^k - (j:ℝ)^k

def covariance (n k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((min i.val j.val+1:ℕ):ℝ)^k

def summation (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => if j ≤ i then 1 else 0

theorem innovation_pos (k : ℕ) (hk : 0 < k) (j : ℕ) : 0 < innovation k j := by
  unfold innovation
  apply sub_pos.mpr
  exact pow_lt_pow_left₀ (by exact_mod_cast Nat.lt_succ_self j) (by positivity) (by omega)

theorem innovation_sum (k : ℕ) (hk : 0 < k) (m : ℕ) :
    ∑ j ∈ range m, innovation k j = (m:ℝ)^k := by
  simp only [innovation]
  rw [sum_range_sub (fun j : ℕ => (j:ℝ)^k) m]
  simp [Nat.ne_of_gt hk]

theorem prefix_sum (w : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n) :
    (∑ j ∈ range n, if j < m then w j else 0) = ∑ j ∈ range m, w j := by
  rw [← sum_filter]
  congr 1
  ext j
  simp only [mem_filter, mem_range]
  omega

theorem covariance_factorization (n k : ℕ) (hk : 0 < k) :
    covariance n k = summation n * Matrix.diagonal (fun j : Fin n => innovation k j.val) *
      (summation n).transpose := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  have he : (∑ l : Fin n, summation n i l * innovation k l.val * summation n j l) =
      ∑ l : Fin n, if l.val < min i.val j.val+1 then innovation k l.val else 0 := by
    apply sum_congr rfl
    intro l _
    simp only [summation, Fin.le_def]
    split_ifs <;> simp_all <;> omega
  rw [he, Fin.sum_univ_eq_sum_range (fun l : ℕ => if l < min i.val j.val+1 then innovation k l else 0),
    prefix_sum _ _ _ (by omega), innovation_sum k hk]
  rfl

theorem covariance_power_brownian (n k : ℕ) : covariance n k =
    FractionalCovarianceMatrices.covariancePower (1/2:ℝ) (fun i : Fin n => ((i.val+1:ℕ):ℝ)) k := by
  ext i j
  rw [FractionalCovarianceMatrices.covariancePower,
    FractionalCovarianceMatrices.brownian_covariance _ _ (by positivity) (by positivity)]
  congr 1
  simp only [covariance, Nat.cast_add, Nat.cast_one, Nat.cast_min, min_add_add_right]

def comparisonRatio (k l j : ℕ) : ℝ := innovation k j / innovation l j

theorem comparisonRatio_identity (k l j : ℕ) (hl : 0 < l) :
    comparisonRatio k l j * innovation l j = innovation k j := by
  exact div_mul_cancel₀ _ (ne_of_gt (innovation_pos l hl j))

theorem adjacent_ratio_two : comparisonRatio 3 2 1 = (7/3:ℝ) := by
  norm_num [comparisonRatio, innovation]

theorem adjacent_ratio_ne_innovation : comparisonRatio 3 2 1 ≠ innovation 3 1 := by
  norm_num [comparisonRatio, innovation]


def predecessor {n : ℕ} (j : Fin n) : Fin n := ⟨j.val-1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩

def differenceVector {n : ℕ} (j : Fin n) : Fin n → ℝ :=
  Pi.single j 1 - if j.val = 0 then 0 else Pi.single (predecessor j) 1

theorem differenceVector_ne_zero {n : ℕ} (j : Fin n) : differenceVector j ≠ 0 := by
  intro he
  have hv := congrFun he j
  by_cases hj : j.val = 0
  · simp [differenceVector, hj] at hv
  · have hp : predecessor j ≠ j := by
      intro h
      have := congrArg Fin.val h
      simp only [predecessor] at this
      omega
    simp [differenceVector, hj, Pi.single_apply, hp, Ne.symm hp] at hv

theorem covariance_difference_action {n : ℕ} (k : ℕ) (hk : 0 < k) (j : Fin n) :
    covariance n k *ᵥ differenceVector j =
      innovation k j.val • (fun i : Fin n => summation n i j) := by
  rw [differenceVector, Matrix.mulVec_sub, Matrix.mulVec_single_one]
  funext i
  by_cases hj : j.val = 0
  · simp [hj, covariance, summation, Fin.le_def, innovation, Nat.ne_of_gt hk]
  · simp only [hj, ↓reduceIte, Matrix.mulVec_single_one, Pi.sub_apply, Matrix.col_apply,
      covariance, predecessor, Pi.smul_apply, smul_eq_mul, summation, Fin.le_def]
    by_cases hji : j.val ≤ i.val
    · rw [if_pos hji, min_eq_right hji, min_eq_right (by omega : j.val-1 ≤ i.val)]
      have he : j.val-1+1=j.val := by omega
      simp only [he, mul_one, innovation]
    · rw [if_neg hji, min_eq_left (by omega : i.val ≤ j.val),
        min_eq_left (by omega : i.val ≤ j.val-1)]
      simp

/-- Genuine generalized eigenpair of two actual covariance-power matrices.
The nonzero vector is independent of k and l; the comparison value is a ratio. -/
theorem generalized_eigenpair {n : ℕ} (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (j : Fin n) :
    differenceVector j ≠ 0 ∧
      covariance n k *ᵥ differenceVector j =
        comparisonRatio k l j.val • (covariance n l *ᵥ differenceVector j) := by
  refine ⟨differenceVector_ne_zero j, ?_⟩
  rw [covariance_difference_action k hk, covariance_difference_action l hl,
    smul_smul, comparisonRatio_identity k l j.val hl]
end OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers
