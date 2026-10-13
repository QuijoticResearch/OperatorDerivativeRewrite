import Foundation.FractionalSpectralGeometry
import Mathlib.Analysis.Matrix.Order

/-! Finite fractional covariance matrices and their integer Hadamard powers.
These are covariance/energy matrices, not an identification of Gaussian OU
Gamma iterations with fractional-time dynamics. -/
noncomputable section
open Matrix
namespace OperatorDerivativeRewrite.Foundation.FractionalCovarianceMatrices
open FractionalSpectralGeometry
variable {ι : Type*} [Fintype ι]

def covarianceMatrix (H : ℝ) (t : ι → ℝ) : Matrix ι ι ℝ := fun i j => covariance H (t i) (t j)

def covariancePower (H : ℝ) (t : ι → ℝ) (k : ℕ) : Matrix ι ι ℝ :=
  fun i j => (covariance H (t i) (t j))^k

theorem covarianceMatrix_posSemidef (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ι → ℝ) :
    (covarianceMatrix H t).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp [Matrix.IsHermitian, Matrix.conjTranspose_apply, covarianceMatrix, covariance_symm]
  · intro c
    simpa only [dotProduct, Matrix.mulVec, covarianceMatrix, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using covariance_positive H hH0 hH1 t c

theorem covariancePower_posSemidef (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ι → ℝ) (k : ℕ) :
    (covariancePower H t k).PosSemidef := by
  induction k with
  | zero =>
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j; simp [covariancePower, Matrix.conjTranspose_apply]
    · intro c
      have hp : 0 ≤ (∑ i, c i)^2 := sq_nonneg _
      simpa [dotProduct, Matrix.mulVec, covariancePower, pow_two, Finset.sum_mul] using hp
  | succ k hk =>
    have he : covariancePower H t (k+1) = (covariancePower H t k).hadamard (covarianceMatrix H t) := by
      ext i j; simp [covariancePower, covarianceMatrix, Matrix.hadamard_apply, pow_succ]
    rw [he]
    exact hk.hadamard (covarianceMatrix_posSemidef H hH0 hH1 t)

theorem covariancePower_energy_nonneg (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (t : ι → ℝ) (k : ℕ) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * (covariance H (t i) (t j))^k := by
  have he := (covariancePower_posSemidef H hH0 hH1 t k).dotProduct_mulVec_nonneg c
  simpa only [dotProduct, Matrix.mulVec, covariancePower, Pi.star_apply, star_trivial,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using he

theorem brownian_covariance (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    covariance (1/2:ℝ) s t = min s t := by
  simp only [covariance, show 2*(1/2:ℝ)=1 by norm_num, Real.rpow_one,
    abs_of_nonneg hs, abs_of_nonneg ht]
  by_cases h : s ≤ t
  · rw [abs_of_nonneg (sub_nonneg.mpr h), min_eq_left h]; ring
  · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h)), min_eq_right (le_of_not_ge h)]; ring


/-- A concrete signed-Hurst kernel is not a covariance kernel of a probability
process: the two-point quadratic form is strictly negative. -/
theorem hurst_two_negative_energy :
    (∑ i : Fin 2, ∑ j : Fin 2,
      (![2,-1] : Fin 2 → ℝ) i * (![2,-1] : Fin 2 → ℝ) j *
        covariance 2 ((![1,2] : Fin 2 → ℝ) i) ((![1,2] : Fin 2 → ℝ) j)) = -12 := by
  norm_num [Fin.sum_univ_two, covariance, show (2:ℝ)*2=(4:ℕ) by norm_num, Real.rpow_natCast]
end OperatorDerivativeRewrite.Foundation.FractionalCovarianceMatrices
