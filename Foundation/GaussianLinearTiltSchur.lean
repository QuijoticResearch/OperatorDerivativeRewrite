import Foundation.GaussianTiltL2Domain
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Actual tilted Gaussian covariance, inverse precision, and exact scalar Schur energies. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix
namespace OperatorDerivativeRewrite.Foundation.GaussianLinearTiltSchur
open InfiniteGaussian GaussianTimeProcess GaussianCore GaussianRandomDensityKernel
  GaussianDensityTranslation GaussianLinearTiltLaw
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Qlinear := Qlinear_probability

def precisionMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 1]
def covarianceMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 2]
def coordinate : Fin 2 → SampleSpace → ℝ := ![process 1, process 2-process 1]
def energy (x y : ℝ) : ℝ := 2*x^2+2*x*y+y^2

theorem first_memLp : MemLp (process 1) 2 Qlinear :=
  first_law.memLp (memLp_id_gaussianReal 2)

theorem second_memLp : MemLp (process 2) 2 Qlinear :=
  second_law.memLp (memLp_id_gaussianReal 2)

theorem first_variance : Var[process 1; Qlinear] = 1 := by
  rw [first_law.variance_eq, variance_id_gaussianReal]
  norm_num

theorem second_variance : Var[process 2; Qlinear] = 1 := by
  rw [second_law.variance_eq, variance_id_gaussianReal]
  norm_num

theorem observation_covariance : cov[process 1, process 2; Qlinear] = 0 :=
  observations_independent.covariance_eq_zero first_memLp second_memLp

theorem first_increment_covariance : cov[process 1, process 2-process 1; Qlinear] = -1 := by
  rw [covariance_sub_right first_memLp second_memLp first_memLp, observation_covariance,
    covariance_self first_memLp.aemeasurable, first_variance]
  norm_num

theorem increment_variance : Var[process 2-process 1; Qlinear] = 2 := by
  have h := observations_independent.symm.covariance_eq_zero second_memLp first_memLp
  rw [variance_sub second_memLp first_memLp, first_variance, second_variance, h]
  norm_num

theorem actual_covariance_matrix (i j : Fin 2) :
    cov[coordinate i, coordinate j; Qlinear] = covarianceMatrix i j := by
  fin_cases i <;> fin_cases j
  · simpa [coordinate, covarianceMatrix, covariance_self first_memLp.aemeasurable]
      using first_variance
  · simpa [coordinate, covarianceMatrix] using first_increment_covariance
  · simpa [coordinate, covarianceMatrix, covariance_comm] using first_increment_covariance
  · simpa [coordinate, covarianceMatrix,
      covariance_self (second_memLp.sub first_memLp).aemeasurable] using increment_variance

theorem precision_covariance : precisionMatrix * covarianceMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [precisionMatrix, covarianceMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem covariance_precision : covarianceMatrix * precisionMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [precisionMatrix, covarianceMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem precision_det : precisionMatrix.det = 1 := by
  norm_num [precisionMatrix, Matrix.det_fin_two]

theorem energy_quadratic_form (x y : ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, ![x,y] i * precisionMatrix i j * ![x,y] j) = energy x y := by
  simp [Fin.sum_univ_two, precisionMatrix, energy]
  ring

theorem completed_square_y (x y : ℝ) : energy x y = x^2+(y+x)^2 := by
  dsimp [energy]
  ring

theorem completed_square_x (x y : ℝ) : energy x y = 2*(x+y/2)^2+y^2/2 := by
  dsimp [energy]
  ring

theorem minimize_y (x : ℝ) :
    (∀ y, x^2 ≤ energy x y) ∧ energy x (-x) = x^2 := by
  constructor
  · intro y
    rw [completed_square_y]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · rw [completed_square_y]
    simp

theorem minimize_x (y : ℝ) :
    (∀ x, y^2/2 ≤ energy x y) ∧ energy (-y/2) y = y^2/2 := by
  constructor
  · intro x
    rw [completed_square_x]
    nlinarith [sq_nonneg (x+y/2)]
  · rw [completed_square_x]
    ring

theorem schur_values :
    precisionMatrix 0 0 - precisionMatrix 0 1 * (precisionMatrix 1 1)⁻¹ *
      precisionMatrix 1 0 = 1 ∧
    precisionMatrix 1 1 - precisionMatrix 1 0 * (precisionMatrix 0 0)⁻¹ *
      precisionMatrix 0 1 = 1/2 := by
  norm_num [precisionMatrix]

theorem tilted_pdf_completed_square (x y : ℝ) :
    gaussianPDFReal 0 1 x * gaussianPDFReal 0 1 y * kernel x y =
      gaussianPDFReal 0 1 x * gaussianPDFReal 0 1 (y+x) := by
  rw [mul_assoc, pdf_product]
  simp [gaussianPDFReal, sub_neg_eq_add]

end OperatorDerivativeRewrite.Foundation.GaussianLinearTiltSchur
