import Foundation.BrownianCovariancePowers

/-! Exact covariance-matrix obstruction to universally decreasing curvature
under stable subordination. These use the ORIGINAL fractional covariance,
not a newly postulated kernel or an assumed full-domain generator theorem. -/
noncomputable section
open Matrix
namespace OperatorDerivativeRewrite.Foundation.FractionalCurvatureSubordinationObstruction
open FractionalCovarianceMatrices

def times : Fin 2 → ℝ := ![1, 2]
def witness : Fin 2 → ℝ := ![1, -1 / 8]
def R (H : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := covarianceMatrix H times
def P (H : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := covariancePower H times 2

theorem R_three_quarters_posSemidef : (R (3 / 4)).PosSemidef :=
  covarianceMatrix_posSemidef (3 / 4) (by norm_num) (by norm_num) times

theorem power_three_halves : (2:ℝ)^(3 / 2:ℝ) = 2 * Real.sqrt 2 := by
  rw [show (3 / 2:ℝ) = 1+1 / 2 by norm_num,Real.rpow_add (by norm_num),Real.rpow_one,
    ← Real.sqrt_eq_rpow]

theorem R_three_quarters : R (3 / 4) = !![1,Real.sqrt 2;Real.sqrt 2,2 * Real.sqrt 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [R,times,covarianceMatrix,FractionalSpectralGeometry.covariance,
      show (2:ℝ)*(3 / 4)=3 / 2 by norm_num,power_three_halves] <;> ring

theorem P_eq_hadamard (H : ℝ) : P H = (R H).hadamard (R H) := by
  ext i j
  simp only [P,R,covariancePower,covarianceMatrix,Matrix.hadamard_apply,pow_two]

theorem P_three_quarters : P (3 / 4) = !![1,2;2,8] := by
  rw [P_eq_hadamard,R_three_quarters]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.hadamard_apply,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),← pow_two] <;>
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem witness_R_energy : dotProduct witness (R (3 / 4) *ᵥ witness) =
    1 - 7 * Real.sqrt 2 / 32 := by
  rw [R_three_quarters]
  norm_num [dotProduct,Matrix.mulVec,Fin.sum_univ_two,witness]
  ring

theorem witness_P_energy : dotProduct witness (P (3 / 4) *ᵥ witness) = (5 / 8:ℝ) := by
  rw [P_three_quarters]
  norm_num [dotProduct,Matrix.mulVec,Fin.sum_univ_two,witness]

theorem witness_R_positive : 0 < dotProduct witness (R (3 / 4) *ᵥ witness) := by
  rw [witness_R_energy]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]

theorem witness_strict_subunit : dotProduct witness (P (3 / 4) *ᵥ witness) <
    dotProduct witness (R (3 / 4) *ᵥ witness) := by
  rw [witness_R_energy,witness_P_energy]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]

theorem R_half : R (1 / 2) = !![1,1;1,2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [R,times,covarianceMatrix,brownian_covariance]

theorem P_half : P (1 / 2) = !![1,1;1,4] := by
  rw [P_eq_hadamard,R_half]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.hadamard_apply]

theorem cauchy_lower (v : Fin 2 → ℝ) :
    dotProduct v (R (1 / 2) *ᵥ v) ≤ dotProduct v (P (1 / 2) *ᵥ v) := by
  rw [R_half,P_half]
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  nlinarith [sq_nonneg (v 1)]

theorem cauchy_sharp : ∃ v : Fin 2 → ℝ,
    dotProduct v (R (1 / 2) *ᵥ v) = 1 ∧ dotProduct v (P (1 / 2) *ᵥ v) = 1 := by
  refine ⟨![1, 0], ?_, ?_⟩ <;>
    norm_num [R_half, P_half, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

/-- Any valid curvature lower bound at gamma=3 / 2 is strictly below one. -/
theorem lower_bound_strict (κ : ℝ)
    (hκ : κ * dotProduct witness (R (3 / 4) *ᵥ witness) ≤
      dotProduct witness (P (3 / 4) *ᵥ witness)) : κ < 1 := by
  have hp := witness_R_positive
  have hs := witness_strict_subunit
  nlinarith

/-- The manuscript's universal monotonicity is incompatible with its Cauchy
value and even its two-frequency necessary lower-bound inequality. This does
not assert that a full-domain curvature function has been constructed. -/
theorem universal_subordination_incompatible (κ : ℝ → ℝ) (hc : κ 1 = 1)
    (hb : κ (3 / 2) * dotProduct witness (R (3 / 4) *ᵥ witness) ≤
      dotProduct witness (P (3 / 4) *ᵥ witness)) :
    ¬ ∀ γ : ℝ, γ ∈ Set.Ioo 0 2 → ∀ α : ℝ, α ∈ Set.Ioo 0 1 → κ (α*γ) ≤ κ γ := by
  intro h
  have hstep := h (3 / 2) (by norm_num) (2 / 3) (by norm_num)
  norm_num [hc] at hstep
  linarith [lower_bound_strict (κ (3 / 2)) hb]

end OperatorDerivativeRewrite.Foundation.FractionalCurvatureSubordinationObstruction
