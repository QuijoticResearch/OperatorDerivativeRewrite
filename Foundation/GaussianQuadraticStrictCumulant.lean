import Foundation.GaussianQuadraticMatrixContraction

/-! Fixed-coordinate positivity detects every nonzero completed quadratic target. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticStrictCumulant
open InfiniteGaussian GaussianNumberSectors GaussianTimeFieldNorm GaussianDivergenceRecovery
open GaussianLinearFieldDivergenceCompletion GaussianLinearFieldMatrixCoordinates
open GaussianQuadraticRecoverySurjectivity GaussianQuadraticSourceHodge GaussianSourceHodge
open GaussianQuadraticMatrixContraction GaussianQuadraticMatrixApproximation
open GaussianSecondChaosL4 GaussianSecondChaosFourthLower GaussianQuadraticContraction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def source (f : sector 2) : linearGaussianFields :=
  ⟨recovery f.val, recovery_second_chaos_linear f.property⟩

theorem source_coordinates_symmetric (f : sector 2) (i j : ℕ) :
    coordinates (source f) (i,j) = coordinates (source f) (j,i) := by
  have hp : gradientProjection (source f : GaussianVectorL2) = (source f : GaussianVectorL2) :=
    gradientRange.starProjection_eq_self_iff.mpr (recovery_mem_gradientRange f.val)
  have hv : (⟨gradientProjection (source f), gradient_mem (source f).property⟩ : linearGaussianFields) =
      source f := Subtype.ext hp
  have he := coordinates_gradient (source f) i j
  rw [hv] at he
  linarith

theorem linearField_entry {I : Type*} [Fintype I] [DecidableEq I]
    (h : I → CoefficientSpace) (hh : Orthonormal ℝ h) (A : Matrix I I ℝ) (i j : I) :
    inner ℝ (scalarTensor (h i) (firstChaosEmbedding (h j))) (linearField h A) = A i j := by
  simp only [linearField, inner_sum, real_inner_smul_right, scalarTensor_pair_inner,
    firstChaosEmbedding.inner_map_map, orthonormal_iff_ite.mp hh]
  simp [mul_ite, ite_mul]

theorem finite_diagonal_contraction {I : Type*} [Fintype I] [DecidableEq I]
    (h : I → CoefficientSpace) (hh : Orthonormal ℝ h) {A : Matrix I I ℝ}
    (hA : A.IsHermitian) (i : I) :
    inner ℝ (scalarTensor (h i) (firstChaosEmbedding (h i)))
      (recovery (projection 2 (polynomialProduct
        (GaussianFiniteQuadraticL4.matrixCore h A) (GaussianFiniteQuadraticL4.matrixCore h A) : GaussianL2))) =
      4 * ∑ j, (A i j)^2 := by
  rw [matrix_square_projection_recovery h hh, symmetrize_of_hermitian hA,
    real_inner_smul_right, linearField_entry h hh, Matrix.mul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he := congrArg (fun M : Matrix I I ℝ => M i j) hA
  simp only [Matrix.conjTranspose_apply, star_trivial] at he
  rw [he]
  ring

theorem box_contraction_diagonal (f : sector 2) (s : Finset ℕ) (i : s) :
    inner ℝ (matrixUnit (i,i)) (recovery (projection 2
      (polynomialProduct (boxCore s (source f)) (boxCore s (source f)) : GaussianL2))) =
      4 * ∑ j : s, (coordinates (source f) (i,j))^2 := by
  let A : Matrix s s ℝ := fun i j => coordinates (source f) (i,j)
  have hA : A.IsHermitian := by
    change A.conjTranspose = A
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact source_coordinates_symmetric f j i
  exact finite_diagonal_contraction (fun i : s => unit i)
    (units_orthonormal.comp Subtype.val Subtype.val_injective) hA i

theorem box_contraction_entry_lower (f : sector 2) (s : Finset ℕ) (i j : s) :
    4 * (coordinates (source f) (i,j))^2 ≤
      inner ℝ (matrixUnit (i,i)) (recovery (projection 2
        (polynomialProduct (boxCore s (source f)) (boxCore s (source f)) : GaussianL2))) := by
  rw [box_contraction_diagonal]
  have hb : (coordinates (source f) (i,j))^2 ≤
      ∑ k : s, (coordinates (source f) (i,k))^2 :=
    Finset.single_le_sum (fun (k : s) _ => sq_nonneg (coordinates (source f) (i,k)))
      (Finset.mem_univ j)
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

theorem completed_contraction_entry_lower (f : sector 2) (i j : ℕ) :
    4 * (coordinates (source f) (i,j))^2 ≤
      inner ℝ (matrixUnit (i,i)) (recovery (projection 2 (square f))) := by
  have hs := square_approximation_tendsto f
  have hp := (projection 2).continuous.continuousAt.tendsto.comp hs
  have hr := recoveryOperator.continuous.continuousAt.tendsto.comp hp
  have ht := (innerSL ℝ (matrixUnit (i,i))).continuous.continuousAt.tendsto.comp hr
  apply ge_of_tendsto ht
  filter_upwards [eventually_ge_atTop (max i j + 1)] with n hn
  have hi : i ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hj : j ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  change 4 * (coordinates (source f) (i,j))^2 ≤
    inner ℝ (matrixUnit (i,i)) (recovery (projection 2 (square (approximation f n))))
  rw [show square (approximation f n) =
    (polynomialProduct (boxCore (Finset.range n) (source f))
      (boxCore (Finset.range n) (source f)) : GaussianL2) from square_polynomial _ _]
  exact box_contraction_entry_lower f (Finset.range n) ⟨i,hi⟩ ⟨j,hj⟩

theorem contraction_zero_imp_target_zero (f : sector 2)
    (hf : projection 2 (square f) = 0) : f.val = 0 := by
  have hc (i j : ℕ) : coordinates (source f) (i,j) = 0 := by
    have hl := completed_contraction_entry_lower f i j
    rw [hf] at hl
    change 4 * (coordinates (source f) (i,j))^2 ≤
      inner ℝ (matrixUnit (i,i)) (recoveryOperator 0) at hl
    rw [map_zero, inner_zero_right] at hl
    have hz : (coordinates (source f) (i,j))^2 = 0 := by nlinarith [sq_nonneg (coordinates (source f) (i,j))]
    exact sq_eq_zero_iff.mp hz
  have hco : coordinates (source f) = 0 := by
    apply lp.ext
    funext p
    exact hc p.1 p.2
  have hn : ‖(source f : GaussianVectorL2)‖ = 0 := by
    have he := coordinates_norm (source f)
    rw [hco, norm_zero] at he
    exact he.symm
  have he := second_recovery_energy f.property
  change ‖(source f : GaussianVectorL2)‖^2 = (1/2 : ℝ) * ‖f.val‖^2 at he
  rw [hn, zero_pow (by decide : (2 : ℕ) ≠ 0)] at he
  apply norm_eq_zero.mp
  have hz : ‖f.val‖^2 = 0 := by linarith
  exact sq_eq_zero_iff.mp hz

theorem nonzero_contraction (f : sector 2) (hf : f.val ≠ 0) :
    projection 2 (square f) ≠ 0 := by
  exact fun h => hf (contraction_zero_imp_target_zero f h)

theorem strict_fourth_moment (f : sector 2) (hf : f.val ≠ 0) :
    3 * (‖f.val‖^2)^2 < ∫ ω, (f.val ω)^4 ∂gaussianProduct := by
  rw [completed_fourth_moment]
  have hp : 0 < ‖projection 2 (square f)‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (nonzero_contraction f hf))
  linarith
end OperatorDerivativeRewrite.Foundation.GaussianQuadraticStrictCumulant
