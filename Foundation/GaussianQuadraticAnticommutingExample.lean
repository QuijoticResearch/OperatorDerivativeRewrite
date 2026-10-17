import Foundation.GaussianQuadraticCovarianceEquality
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Anticommuting symmetric matrices give dependent orthogonal quadratic targets
with vanishing mixed second-chaos contraction. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticAnticommutingExample
open InfiniteGaussian GaussianNumberSectors GaussianSecondChaosL4 GaussianSecondChaosProduct
open GaussianQuadraticMatrixContraction GaussianQuadraticSquareCovariance
open GaussianQuadraticCovarianceEquality GaussianQuadraticSourceHodge
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def B : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

def directions (i : Fin 2) : CoefficientSpace := GaussianLinearFieldMatrixCoordinates.unit i.val

theorem directions_orthonormal : Orthonormal ℝ directions :=
  GaussianLinearFieldMatrixCoordinates.units_orthonormal.comp Fin.val Fin.val_injective

theorem A_hermitian : A.IsHermitian := by
  change A.conjTranspose = A
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, Matrix.conjTranspose_apply]

theorem B_hermitian : B.IsHermitian := by
  change B.conjTranspose = B
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [B, Matrix.conjTranspose_apply]

theorem anticommutator_zero : A*B+B*A = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, B, Matrix.mul_apply, Fin.sum_univ_two]

theorem product_nonzero : A*B ≠ 0 := by
  intro he
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) he
  norm_num [A, B, Matrix.mul_apply, Fin.sum_univ_two] at hc

def f : sector 2 := matrixSectorMap directions A
def g : sector 2 := matrixSectorMap directions B

theorem orthogonal : inner ℝ f.val g.val = 0 := by
  change inner ℝ (quadraticTarget directions A) (quadraticTarget directions B) = 0
  rw [hermitian_target_inner directions directions_orthonormal A_hermitian B_hermitian]
  norm_num [A, B, Fin.sum_univ_two]

theorem f_variance : ‖f.val‖^2 = 4 := by
  change ‖quadraticTarget directions A‖^2 = 4
  rw [hermitian_target_energy directions directions_orthonormal A_hermitian]
  norm_num [A, Fin.sum_univ_two]

theorem g_variance : ‖g.val‖^2 = 4 := by
  change ‖quadraticTarget directions B‖^2 = 4
  rw [hermitian_target_energy directions directions_orthonormal B_hermitian]
  norm_num [B, Fin.sum_univ_two]

theorem mixed_contraction_zero : projection 2 (product f g) = 0 := by
  rw [show f = matrixSectorMap directions A from rfl, show g = matrixSectorMap directions B from rfl,
    hermitian_mixed_projection_two directions directions_orthonormal A_hermitian B_hermitian,
    anticommutator_zero]
  change (2 : ℝ) • GaussianFiniteQuadraticL4.matrixTargetMap directions 0 = 0
  rw [map_zero, smul_zero]

theorem square_contraction_pairing :
    inner ℝ (projection 2 (square f)) (projection 2 (square g)) = 64 := by
  rw [show f = matrixSectorMap directions A from rfl, show g = matrixSectorMap directions B from rfl,
    matrix_contraction_pairing directions directions_orthonormal A_hermitian B_hermitian]
  norm_num [A, B, Matrix.mul_apply, Fin.sum_univ_two]

theorem square_covariance : inner ℝ (square f) (square g) - ‖f.val‖^2 * ‖g.val‖^2 = 32 := by
  rw [covariance_polarization, orthogonal, mixed_contraction_zero, square_contraction_pairing]
  norm_num

theorem cross_fourth_moment :
    (∫ ω, (f.val ω)^2 * (g.val ω)^2 ∂gaussianProduct) = 48 := by
  rw [← square_inner_integral]
  have he := square_covariance
  rw [f_variance, g_variance] at he
  linarith

theorem not_independent : ¬ProbabilityTheory.IndepFun f.val g.val gaussianProduct := by
  intro hi
  exact product_nonzero (matrix_independent_implies_mul_zero directions directions_orthonormal
    A_hermitian B_hermitian hi)

theorem f_class : f.val = mixedTarget (directions 0) (directions 0) -
    mixedTarget (directions 1) (directions 1) := by
  change quadraticTarget directions A = _
  simp [quadraticTarget, A, Fin.sum_univ_two, sub_eq_add_neg]

theorem g_class : g.val = (2 : ℝ) • mixedTarget (directions 0) (directions 1) := by
  change quadraticTarget directions B = _
  simp [quadraticTarget, B, Fin.sum_univ_two,
    GaussianFiniteQuadraticL4.mixedTarget_comm, two_smul]

theorem f_coeFn : f.val =ᵐ[gaussianProduct] fun ω =>
    (firstChaosEmbedding (directions 0) ω)^2 - (firstChaosEmbedding (directions 1) ω)^2 := by
  rw [f_class]
  filter_upwards [Lp.coeFn_sub (mixedTarget (directions 0) (directions 0))
      (mixedTarget (directions 1) (directions 1)),
    mixedTarget_coeFn (directions 0) (directions 0),
    mixedTarget_coeFn (directions 1) (directions 1)] with ω hs h0 h1
  rw [hs, Pi.sub_apply, h0, h1]
  simp only [real_inner_self_eq_norm_sq, directions_orthonormal.norm_eq_one, one_pow]
  ring

theorem g_coeFn : g.val =ᵐ[gaussianProduct] fun ω =>
    2 * firstChaosEmbedding (directions 0) ω * firstChaosEmbedding (directions 1) ω := by
  rw [g_class]
  filter_upwards [Lp.coeFn_smul (2 : ℝ) (mixedTarget (directions 0) (directions 1)),
    mixedTarget_coeFn (directions 0) (directions 1)] with ω hs hm
  rw [hs, Pi.smul_apply, smul_eq_mul, hm]
  have hi : inner ℝ (directions 0) (directions 1) = 0 := by
    simpa using orthonormal_iff_ite.mp directions_orthonormal 0 1
  rw [hi]
  ring

theorem radial_square_identity : ∀ᵐ ω ∂gaussianProduct,
    (f.val ω)^2 + (g.val ω)^2 =
      ((firstChaosEmbedding (directions 0) ω)^2 + (firstChaosEmbedding (directions 1) ω)^2)^2 := by
  filter_upwards [f_coeFn, g_coeFn] with ω hf hg
  rw [hf, hg]
  ring
end OperatorDerivativeRewrite.Foundation.GaussianQuadraticAnticommutingExample
