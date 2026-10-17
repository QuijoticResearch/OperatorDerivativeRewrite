import Foundation.DoubleSkewGaussianBridge
import Foundation.GaussianFiniteQuadraticL4
import Foundation.BochnerL2Dominated

/-! Complete tensor symmetrization and the actual Gaussian determinant fourth moment. -/
noncomputable section
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.TensorSymmetryDeterminantMoments
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
open DoubleSkewGaussianBridge GaussianQuadraticSourceHodge InfiniteGaussian
open GaussianFiniteQuadraticL4 GaussianDivergenceRecovery GaussianSourceHodge
open GaussianTimeFieldNorm
open MeasureTheory

def skewPart {I : Type*} (A : Matrix I I ℝ) : Matrix I I ℝ := fun i j => (A i j-A j i)/2

theorem tensor_symmetrization {L C : Type*} (A : Matrix L L ℝ) (B : Matrix C C ℝ) :
    symmetrize (tensor A B)=tensor (symmetrize A) (symmetrize B)+tensor (skewPart A) (skewPart B) := by
  ext i j
  simp only [symmetrize, tensor, skewPart, Matrix.add_apply]
  ring

theorem matrix_parts {I : Type*} (A : Matrix I I ℝ) : symmetrize A+skewPart A=A := by
  ext i j
  simp only [symmetrize, skewPart, Matrix.add_apply]
  ring

theorem J_symmetrize : symmetrize J=0 := by
  ext i j
  unfold symmetrize
  rw [J_skew i j]
  simp

theorem J_skewPart : skewPart J=J := by
  ext i j
  unfold skewPart
  rw [J_skew i j]
  ring

theorem componentwise_symmetrization_fails :
    symmetrize (tensor J J) ≠ tensor (symmetrize J) (symmetrize J) := by
  have hz : tensor (symmetrize J) (symmetrize J)=0 := by
    rw [J_symmetrize]
    ext i j
    simp [tensor]
  rw [hz]
  change symmetrize T ≠ 0
  rw [T_symmetrize]
  intro ht
  have hh := sameCorner_contraction
  rw [ht] at hh
  norm_num [ChristoffelSkewCancellation.contraction] at hh

theorem recovery_tensor_parts {L C : Type*} [Fintype L] [Fintype C]
    (A : Matrix L L ℝ) (B : Matrix C C ℝ) (h : L×C → CoefficientSpace) :
    recovery (quadraticTarget h (tensor A B))=
      linearField h (tensor (symmetrize A) (symmetrize B))+
        linearField h (tensor (skewPart A) (skewPart B)) := by
  rw [quadraticTarget_recovery, tensor_symmetrization, linearField_add]

theorem gradient_tensor_parts {L C : Type*} [Fintype L] [Fintype C]
    (A : Matrix L L ℝ) (B : Matrix C C ℝ) (h : L×C → CoefficientSpace) :
    gradientProjection (linearField h (tensor A B))=
      linearField h (tensor (symmetrize A) (symmetrize B))+
        linearField h (tensor (skewPart A) (skewPart B)) := by
  rw [linearField_gradientProjection, tensor_symmetrization, linearField_add]

theorem T_hermitian : T.IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact T_symmetric i j

theorem T_eigenvalue_square (i : Fin 2×Fin 2) : (T_hermitian.eigenvalues i)^2=1 := by
  let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin 2×Fin 2) (Fin 2×Fin 2) ℝ)
    (star T_hermitian.eigenvectorUnitary)
  have hf : f T=Matrix.diagonal (fun j => T_hermitian.eigenvalues j) := by
    simpa [f] using T_hermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hs := congrArg f T_square
  rw [map_mul, map_one, hf, Matrix.diagonal_mul_diagonal] at hs
  have he := congrArg (fun M : Matrix (Fin 2×Fin 2) (Fin 2×Fin 2) ℝ => M i i) hs
  simpa [pow_two] using he

theorem T_eigenvalue_fourth (i : Fin 2×Fin 2) : (T_hermitian.eigenvalues i)^4=1 := by
  rw [show (4:ℕ)=2*2 by decide, pow_mul, T_eigenvalue_square]
  norm_num

theorem T_eigen_sums :
    (∑ i, (T_hermitian.eigenvalues i)^2)=4 ∧ (∑ i, (T_hermitian.eigenvalues i)^4)=4 := by
  simp [T_eigenvalue_square, T_eigenvalue_fourth]

def determinantCore (h : Fin 2×Fin 2 → CoefficientSpace) : polynomialCylindricalDomain := matrixCore h T

theorem determinantCore_eq (h : Fin 2×Fin 2 → CoefficientSpace) :
    (determinantCore h : GaussianL2)=quadraticTarget h T := matrixCore_eq_target h T

theorem determinant_fourth_moment (h : Fin 2×Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h) :
    ‖(polynomialProduct (determinantCore h) (determinantCore h) : GaussianL2)‖^2=384 := by
  rw [determinantCore, hermitian_fourth_moment T_hermitian h hh,
    T_eigen_sums.1, T_eigen_sums.2]
  norm_num

theorem determinant_fourth_ratio (h : Fin 2×Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h) :
    ‖(polynomialProduct (determinantCore h) (determinantCore h) : GaussianL2)‖^2=
      6*(‖(determinantCore h : GaussianL2)‖^2)^2 := by
  rw [determinant_fourth_moment h hh, determinantCore_eq, gaussian_variance h hh]
  norm_num

theorem determinant_not_gaussian_fourth_identity (h : Fin 2×Fin 2 → CoefficientSpace)
    (hh : Orthonormal ℝ h) :
    ‖(polynomialProduct (determinantCore h) (determinantCore h) : GaussianL2)‖^2 ≠
      3*(‖(determinantCore h : GaussianL2)‖^2)^2 := by
  rw [determinant_fourth_moment h hh, determinantCore_eq, gaussian_variance h hh]
  norm_num

theorem actual_determinant_fourth_moment :
    ‖(polynomialProduct (determinantCore directions) (determinantCore directions) : GaussianL2)‖^2=384 :=
  determinant_fourth_moment directions directions_orthonormal

theorem determinant_square_ae (h : Fin 2×Fin 2 → CoefficientSpace) :
    (polynomialProduct (determinantCore h) (determinantCore h) : GaussianL2) =ᵐ[gaussianProduct]
      fun ω => (quadraticTarget h T ω)^2 := by
  filter_upwards [polynomialProductL2_coeFn (determinantCore h) (determinantCore h)] with ω hω
  change polynomialProductL2 (determinantCore h) (determinantCore h) ω=_
  rw [hω]
  change (determinantCore h : GaussianL2) ω*(determinantCore h : GaussianL2) ω=_
  simp only [determinantCore_eq, pow_two]

theorem determinant_fourth_integral (h : Fin 2×Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h) :
    (∫ ω, (quadraticTarget h T ω)^4 ∂gaussianProduct)=384 := by
  have he := determinant_fourth_moment h hh
  rw [BochnerL2Dominated.norm_sq_integral] at he
  have ha : (fun ω => ‖(polynomialProduct (determinantCore h) (determinantCore h) : GaussianL2) ω‖^2)
      =ᵐ[gaussianProduct] (fun ω => (quadraticTarget h T ω)^4) := by
    filter_upwards [determinant_square_ae h] with ω hω
    rw [hω]
    simp only [Real.norm_eq_abs, sq_abs]
    ring
  rw [integral_congr_ae ha] at he
  exact he

theorem determinant_fourth_integrable (h : Fin 2×Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h) :
    Integrable (fun ω => (quadraticTarget h T ω)^4) gaussianProduct := by
  by_contra hn
  have hz := integral_undef hn
  rw [determinant_fourth_integral h hh] at hz
  norm_num at hz

theorem actual_determinant_fourth_integral :
    (∫ ω, (quadraticTarget directions T ω)^4 ∂gaussianProduct)=384 :=
  determinant_fourth_integral directions directions_orthonormal

end OperatorDerivativeRewrite.Foundation.TensorSymmetryDeterminantMoments
