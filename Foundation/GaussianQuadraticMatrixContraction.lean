import Foundation.GaussianQuadraticContraction

/-! Actual matrix multiplication realizes the degree-two square contraction. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticMatrixContraction
open InfiniteGaussian GaussianNumberSectors GaussianQuadraticSourceHodge
open GaussianQuadraticSpectralTransport GaussianDiagonalQuadraticL4 GaussianFiniteQuadraticL4
open GaussianQuadraticContraction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem rotated_diagonal_target (h : I → CoefficientSpace) (U : Matrix.unitaryGroup I ℝ)
    (a : I → ℝ) :
    (target (rotatedSources h U) a : GaussianL2) =
      quadraticTarget h (Unitary.conjStarAlgAut ℝ (Matrix I I ℝ) U (Matrix.diagonal a)) := by
  simp only [target, Submodule.coe_sum, Submodule.coe_smul,
    ← mixedTarget_self_wick, rotatedSources, mixedTarget_linear_combination,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  unfold quadraticTarget
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_smul]
  congr 1
  simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal,
    Matrix.star_apply, Matrix.of_apply, star_trivial, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro j _
  simp [Matrix.of_apply, mul_ite, ite_mul]
  <;> ring

theorem spectral_square {A : Matrix I I ℝ} (hA : A.IsHermitian) :
    A * A = Unitary.conjStarAlgAut ℝ (Matrix I I ℝ) hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => (hA.eigenvalues i)^2)) := by
  have he : A = Unitary.conjStarAlgAut ℝ (Matrix I I ℝ) hA.eigenvectorUnitary
      (Matrix.diagonal hA.eigenvalues) := by simpa using hA.spectral_theorem
  calc
    A*A = Unitary.conjStarAlgAut ℝ (Matrix I I ℝ) hA.eigenvectorUnitary (Matrix.diagonal hA.eigenvalues) *
        Unitary.conjStarAlgAut ℝ (Matrix I I ℝ) hA.eigenvectorUnitary (Matrix.diagonal hA.eigenvalues) :=
      congrArg₂ (fun X Y : Matrix I I ℝ => X*Y) he he
    _ = _ := by
      rw [← map_mul, Matrix.diagonal_mul_diagonal]
      congr 2
      funext i
      ring

theorem hermitian_square_projection_two (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    {A : Matrix I I ℝ} (hA : A.IsHermitian) :
    projection 2 (polynomialProduct (matrixCore h A) (matrixCore h A) : GaussianL2) =
      (4 : ℝ) • quadraticTarget h (A*A) := by
  rw [matrixCore_spectral hA, diagonal_square_projection_two _ (rotatedSources_orthonormal h hh _),
    rotated_diagonal_target, spectral_square hA]

theorem matrix_square_projection_two (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    (A : Matrix I I ℝ) :
    projection 2 (polynomialProduct (matrixCore h A) (matrixCore h A) : GaussianL2) =
      (4 : ℝ) • quadraticTarget h (symmetrize A * symmetrize A) := by
  rw [← matrixCore_symmetrize h A]
  exact hermitian_square_projection_two h hh (symmetrize_hermitian A)

theorem quadraticTarget_mem_two (h : I → CoefficientSpace) (A : Matrix I I ℝ) :
    quadraticTarget h A ∈ sector 2 := by
  unfold quadraticTarget
  exact (sector 2).sum_mem fun i _ => (sector 2).sum_mem fun j _ =>
    (sector 2).smul_mem _ (GaussianLinearFieldDivergenceCompletion.mixedTarget_mem_sector_two _ _)

def matrixSectorMap (h : I → CoefficientSpace) : Matrix I I ℝ →ₗ[ℝ] sector 2 :=
  (matrixTargetMap h).codRestrict (sector 2) (quadraticTarget_mem_two h)

theorem hermitian_product_self_projection (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    {A : Matrix I I ℝ} (hA : A.IsHermitian) :
    projection 2 (GaussianSecondChaosProduct.product (matrixSectorMap h A) (matrixSectorMap h A)) =
      (4 : ℝ) • quadraticTarget h (A*A) := by
  have hp : (matrixCore h A : GaussianL2) ∈ sector 2 := by
    rw [matrixCore_eq_target]
    exact quadraticTarget_mem_two h A
  have hf : matrixSectorMap h A = ⟨matrixCore h A, hp⟩ := by
    apply Subtype.ext
    exact (matrixCore_eq_target h A).symm
  rw [hf, GaussianSecondChaosProduct.product_self_eq_square, GaussianSecondChaosL4.square_polynomial]
  exact hermitian_square_projection_two h hh hA

theorem hermitian_mixed_projection_two (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    {A B : Matrix I I ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    projection 2 (GaussianSecondChaosProduct.product (matrixSectorMap h A) (matrixSectorMap h B)) =
      (2 : ℝ) • quadraticTarget h (A*B+B*A) := by
  let L := matrixSectorMap h
  let P := GaussianSecondChaosProduct.product
  have hs := hermitian_product_self_projection h hh (hA.add hB)
  have ha := hermitian_product_self_projection h hh hA
  have hb := hermitian_product_self_projection h hh hB
  have he : P (L A) (L B) = (1/2 : ℝ) •
      (P (L (A+B)) (L (A+B)) - P (L A) (L A) - P (L B) (L B)) := by
    simp only [map_add, P, GaussianSecondChaosProduct.product_add_left,
      GaussianSecondChaosProduct.product_add_right,
      GaussianSecondChaosProduct.product_comm (L B) (L A)]
    module
  change projection 2 (P (L A) (L B)) = _
  rw [he, map_smul, map_sub, map_sub, hs, ha, hb]
  have hm : (A+B)*(A+B) = A*A + B*B + (A*B+B*A) := by noncomm_ring
  rw [hm]
  change (1/2 : ℝ) • (4 • matrixTargetMap h (A*A+B*B+(A*B+B*A)) -
    4 • matrixTargetMap h (A*A) - 4 • matrixTargetMap h (B*B)) =
      2 • matrixTargetMap h (A*B+B*A)
  rw [map_add, map_add]
  module
theorem symmetrize_of_hermitian {A : Matrix I I ℝ} (hA : A.IsHermitian) :
    symmetrize A = A := by
  ext i j
  have he := congrArg (fun M : Matrix I I ℝ => M i j) hA
  simp only [Matrix.conjTranspose_apply, star_trivial] at he
  simp only [symmetrize, he]
  ring

theorem hermitian_target_energy (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    {A : Matrix I I ℝ} (hA : A.IsHermitian) :
    ‖quadraticTarget h A‖^2 = 2 * ∑ i, ∑ j, (A i j)^2 := by
  rw [quadraticTarget_variance, symmetrize_of_hermitian hA, linearField_energy h hh]

theorem hermitian_square_projection_energy (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    {A : Matrix I I ℝ} (hA : A.IsHermitian) :
    ‖projection 2 (polynomialProduct (matrixCore h A) (matrixCore h A) : GaussianL2)‖^2 =
      32 * ∑ i, ∑ j, ((A*A) i j)^2 := by
  have hAA : (A*A).IsHermitian := by simpa only [pow_two] using hA.pow 2
  rw [hermitian_square_projection_two h hh hA, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, hermitian_target_energy h hh hAA]
  ring

theorem matrix_fourth_cumulant_energy (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    (A : Matrix I I ℝ) :
    ‖(polynomialProduct (matrixCore h A) (matrixCore h A) : GaussianL2)‖^2 -
      3 * (‖(matrixCore h A : GaussianL2)‖^2)^2 =
      48 * ∑ i, ∑ j, ((symmetrize A * symmetrize A) i j)^2 := by
  rw [← matrixCore_symmetrize h A]
  rw [matrix_fourth_cumulant h hh,
    hermitian_square_projection_energy h hh (symmetrize_hermitian A)]
  ring

theorem matrix_square_projection_recovery (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    (A : Matrix I I ℝ) :
    GaussianDivergenceRecovery.recovery
      (projection 2 (polynomialProduct (matrixCore h A) (matrixCore h A) : GaussianL2)) =
        (4 : ℝ) • linearField h (symmetrize A * symmetrize A) := by
  have hSS : (symmetrize A * symmetrize A).IsHermitian := by
    simpa only [pow_two] using (symmetrize_hermitian A).pow 2
  rw [matrix_square_projection_two h hh]
  change GaussianDivergenceRecovery.recoveryOperator _ = _
  rw [map_smul]
  change (4 : ℝ) • GaussianDivergenceRecovery.recovery
    (quadraticTarget h (symmetrize A * symmetrize A)) = _
  rw [quadraticTarget_recovery, symmetrize_of_hermitian hSS]
end OperatorDerivativeRewrite.Foundation.GaussianQuadraticMatrixContraction
