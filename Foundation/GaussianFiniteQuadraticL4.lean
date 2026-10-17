import Foundation.GaussianQuadraticSpectralTransport

/-! Sharp uniform fourth-moment bounds for every actual finite Gaussian matrix
quadratic. The antisymmetric part is eliminated by proved observable identities. -/
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianFiniteQuadraticL4
open InfiniteGaussian GaussianQuadraticSourceHodge GaussianQuadraticSpectralTransport
open GaussianDiagonalQuadraticL4
variable {I : Type*} [Fintype I] [DecidableEq I]

def matrixCore (h : I → CoefficientSpace) (A : Matrix I I ℝ) : polynomialCylindricalDomain :=
  ∑ i, ∑ j, A i j • mixedPolynomial (h i) (h j)

theorem matrixCore_eq_target (h : I → CoefficientSpace) (A : Matrix I I ℝ) :
    (matrixCore h A : GaussianL2) = quadraticTarget h A := by
  simp only [matrixCore, Submodule.coe_sum, Submodule.coe_smul]
  rfl

theorem matrixCore_spectral {A : Matrix I I ℝ} (hA : A.IsHermitian) (h : I → CoefficientSpace) :
    matrixCore h A = target (rotatedSources h hA.eigenvectorUnitary) hA.eigenvalues := by
  apply Subtype.ext
  rw [matrixCore_eq_target, quadraticTarget_eq_diagonal hA]

theorem hermitian_fourth_moment {A : Matrix I I ℝ} (hA : A.IsHermitian)
    (h : I → CoefficientSpace) (hh : Orthonormal ℝ h) :
    ‖(polynomialProduct (matrixCore h A) (matrixCore h A) : GaussianL2)‖^2 =
      12 * (∑ i, (hA.eigenvalues i)^2)^2 + 48 * ∑ i, (hA.eigenvalues i)^4 := by
  rw [matrixCore_spectral hA, target_fourth_moment _ (rotatedSources_orthonormal h hh _)]

theorem hermitian_fourth_upper_bound {A : Matrix I I ℝ} (hA : A.IsHermitian)
    (h : I → CoefficientSpace) (hh : Orthonormal ℝ h) :
    ‖(polynomialProduct (matrixCore h A) (matrixCore h A) : GaussianL2)‖^2 ≤
      15 * (‖(matrixCore h A : GaussianL2)‖^2)^2 := by
  rw [matrixCore_spectral hA]
  exact target_fourth_upper_bound _ (rotatedSources_orthonormal h hh _) _

theorem mixedTarget_comm (u v : CoefficientSpace) : mixedTarget u v = mixedTarget v u := by
  apply Lp.ext
  filter_upwards [mixedTarget_coeFn u v, mixedTarget_coeFn v u] with ω huv hvu
  rw [huv, hvu, real_inner_comm u v]
  ring

theorem quadraticTarget_transpose (h : I → CoefficientSpace) (A : Matrix I I ℝ) :
    quadraticTarget h A.transpose = quadraticTarget h A := by
  unfold quadraticTarget
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mixedTarget_comm]
  rfl

def matrixTargetMap (h : I → CoefficientSpace) : Matrix I I ℝ →ₗ[ℝ] GaussianL2 where
  toFun := quadraticTarget h
  map_add' A B := by
    simp only [quadraticTarget, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [quadraticTarget, Matrix.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum,
      RingHom.id_apply]

theorem quadraticTarget_symmetrize (h : I → CoefficientSpace) (A : Matrix I I ℝ) :
    quadraticTarget h (symmetrize A) = quadraticTarget h A := by
  have he : symmetrize A = (1/2 : ℝ) • (A + A.transpose) := by
    ext i j
    simp only [symmetrize, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
    ring
  rw [he]
  change matrixTargetMap h ((1/2 : ℝ) • (A + A.transpose)) = matrixTargetMap h A
  rw [map_smul, map_add]
  change (1/2 : ℝ) • (quadraticTarget h A + quadraticTarget h A.transpose) = _
  rw [quadraticTarget_transpose]
  change (1/2 : ℝ) • (quadraticTarget h A + quadraticTarget h A) = quadraticTarget h A
  rw [← two_smul ℝ, smul_smul]
  norm_num

theorem symmetrize_hermitian (A : Matrix I I ℝ) : (symmetrize A).IsHermitian := by
  change (symmetrize A).conjTranspose = symmetrize A
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, symmetrize]
  ring

theorem matrixCore_symmetrize (h : I → CoefficientSpace) (A : Matrix I I ℝ) :
    matrixCore h (symmetrize A) = matrixCore h A := by
  apply Subtype.ext
  rw [matrixCore_eq_target, matrixCore_eq_target, quadraticTarget_symmetrize]

/-- Every finite matrix, including nonsymmetric ones, has the sharp pure-quadratic bound. -/
theorem finite_matrix_fourth_upper_bound (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    (A : Matrix I I ℝ) :
    ‖(polynomialProduct (matrixCore h A) (matrixCore h A) : GaussianL2)‖^2 ≤
      15 * (‖(matrixCore h A : GaussianL2)‖^2)^2 := by
  rw [← matrixCore_symmetrize h A]
  exact hermitian_fourth_upper_bound (symmetrize_hermitian A) h hh

theorem finite_matrix_fourth_lower_bound (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    (A : Matrix I I ℝ) :
    3 * (‖(matrixCore h A : GaussianL2)‖^2)^2 ≤
      ‖(polynomialProduct (matrixCore h A) (matrixCore h A) : GaussianL2)‖^2 := by
  rw [← matrixCore_symmetrize h A, matrixCore_spectral (symmetrize_hermitian A)]
  exact target_fourth_lower_bound _ (rotatedSources_orthonormal h hh _) _

end OperatorDerivativeRewrite.Foundation.GaussianFiniteQuadraticL4
