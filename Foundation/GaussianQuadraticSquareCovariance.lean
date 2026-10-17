import Foundation.GaussianQuadraticStrictCumulant
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Polarization of the completed fourth cumulant identifies mixed square covariance. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticSquareCovariance
open InfiniteGaussian GaussianNumberSectors GaussianSecondChaosL4 GaussianSecondChaosProduct
open GaussianQuadraticContraction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem covariance_polarization (f g : sector 2) :
    inner ℝ (square f) (square g) - ‖f.val‖^2 * ‖g.val‖^2 =
      2 * (inner ℝ f.val g.val)^2 +
      (1/2 : ℝ) * inner ℝ (projection 2 (square f)) (projection 2 (square g)) +
      ‖projection 2 (product f g)‖^2 := by
  have hplus := completed_fourth_cumulant (f+g)
  have hminus := completed_fourth_cumulant (f+(-1 : ℝ) • g)
  have hf := completed_fourth_cumulant f
  have hg := completed_fourth_cumulant g
  have hm := product_energy_inner f g
  simp only [← product_self_eq_square, product_add_left, product_add_right,
    product_smul_left, product_smul_right, product_comm g f, map_add, map_smul,
    Submodule.coe_add, Submodule.coe_smul, ← real_inner_self_eq_norm_sq,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm] at hplus hminus hf hg hm ⊢
  nlinarith

theorem second_chaos_recovery_inner (f g : sector 2) :
    inner ℝ f.val g.val = 2 * inner ℝ (GaussianDivergenceRecovery.recovery f.val)
      (GaussianDivergenceRecovery.recovery g.val) := by
  have hf := GaussianQuadraticRecoverySurjectivity.second_recovery_energy f.property
  have hg := GaussianQuadraticRecoverySurjectivity.second_recovery_energy g.property
  have hs := GaussianQuadraticRecoverySurjectivity.second_recovery_energy (f+g).property
  change ‖GaussianDivergenceRecovery.recoveryOperator (f.val+g.val)‖^2 =
    (1/2 : ℝ) * ‖f.val+g.val‖^2 at hs
  rw [map_add, norm_add_sq_real, norm_add_sq_real] at hs
  change ‖GaussianDivergenceRecovery.recoveryOperator f.val‖^2 = (1/2 : ℝ) * ‖f.val‖^2 at hf
  change ‖GaussianDivergenceRecovery.recoveryOperator g.val‖^2 = (1/2 : ℝ) * ‖g.val‖^2 at hg
  change inner ℝ f.val g.val = 2 * inner ℝ
    (GaussianDivergenceRecovery.recoveryOperator f.val) (GaussianDivergenceRecovery.recoveryOperator g.val)
  linarith

open GaussianQuadraticMatrixContraction GaussianQuadraticSourceHodge GaussianFiniteQuadraticL4

theorem frobenius_pair_trace {I : Type*} [Fintype I] (A B : Matrix I I ℝ) :
    (∑ i, ∑ j, A i j * B i j) = Matrix.trace (A.transpose * B) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem hermitian_square_pair_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    {A B : Matrix I I ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    0 ≤ ∑ i, ∑ j, (A*A) i j * (B*B) i j := by
  have hta : A.transpose = A := by
    ext i j
    have he := congrArg (fun M : Matrix I I ℝ => M i j) hA
    simpa only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial] using he
  have htb : B.transpose = B := by
    ext i j
    have he := congrArg (fun M : Matrix I I ℝ => M i j) hB
    simpa only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial] using he
  have he : Matrix.trace ((A*B).transpose * (A*B)) = Matrix.trace ((A*A)*(B*B)) := by
    rw [Matrix.transpose_mul, hta, htb]
    calc
      Matrix.trace ((B*A)*(A*B)) = Matrix.trace (B*((A*A)*B)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace (((A*A)*B)*B) := Matrix.trace_mul_comm _ _
      _ = _ := by rw [Matrix.mul_assoc]
  have hs : 0 ≤ ∑ i, ∑ j, (A*B) i j * (A*B) i j := by
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
  rw [frobenius_pair_trace, he] at hs
  rw [frobenius_pair_trace, Matrix.transpose_mul, hta]
  exact hs

theorem hermitian_target_inner {I : Type*} [Fintype I] [DecidableEq I]
    (h : I → CoefficientSpace) (hh : Orthonormal ℝ h) {A B : Matrix I I ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    inner ℝ (quadraticTarget h A) (quadraticTarget h B) =
      2 * ∑ i, ∑ j, A i j * B i j := by
  have he := second_chaos_recovery_inner (matrixSectorMap h A) (matrixSectorMap h B)
  change inner ℝ (quadraticTarget h A) (quadraticTarget h B) =
    2 * inner ℝ (GaussianDivergenceRecovery.recovery (quadraticTarget h A))
      (GaussianDivergenceRecovery.recovery (quadraticTarget h B)) at he
  rw [quadraticTarget_recovery, quadraticTarget_recovery,
    symmetrize_of_hermitian hA, symmetrize_of_hermitian hB, linearField_inner h hh] at he
  exact he

theorem finite_contraction_pairing_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (h : I → CoefficientSpace) (hh : Orthonormal ℝ h) (A B : Matrix I I ℝ) :
    0 ≤ inner ℝ
      (projection 2 (polynomialProduct (matrixCore h A) (matrixCore h A) : GaussianL2))
      (projection 2 (polynomialProduct (matrixCore h B) (matrixCore h B) : GaussianL2)) := by
  have hAA : (symmetrize A * symmetrize A).IsHermitian := by
    simpa only [pow_two] using (symmetrize_hermitian A).pow 2
  have hBB : (symmetrize B * symmetrize B).IsHermitian := by
    simpa only [pow_two] using (symmetrize_hermitian B).pow 2
  rw [matrix_square_projection_two h hh, matrix_square_projection_two h hh,
    real_inner_smul_left, real_inner_smul_right, hermitian_target_inner h hh hAA hBB]
  have hp := hermitian_square_pair_nonneg (symmetrize_hermitian A) (symmetrize_hermitian B)
  positivity

open GaussianSecondChaosFourthLower GaussianQuadraticMatrixApproximation

theorem completed_contraction_pairing_nonneg (f g : sector 2) :
    0 ≤ inner ℝ (projection 2 (square f)) (projection 2 (square g)) := by
  have hf := (projection 2).continuous.continuousAt.tendsto.comp (square_approximation_tendsto f)
  have hg := (projection 2).continuous.continuousAt.tendsto.comp (square_approximation_tendsto g)
  apply ge_of_tendsto (hf.inner hg)
  apply Eventually.of_forall
  intro n
  change 0 ≤ inner ℝ (projection 2 (square (approximation f n)))
    (projection 2 (square (approximation g n)))
  rw [show square (approximation f n) =
    (polynomialProduct (boxCore (Finset.range n) (GaussianQuadraticStrictCumulant.source f))
      (boxCore (Finset.range n) (GaussianQuadraticStrictCumulant.source f)) : GaussianL2)
    from square_polynomial _ _]
  rw [show square (approximation g n) =
    (polynomialProduct (boxCore (Finset.range n) (GaussianQuadraticStrictCumulant.source g))
      (boxCore (Finset.range n) (GaussianQuadraticStrictCumulant.source g)) : GaussianL2)
    from square_polynomial _ _]
  exact finite_contraction_pairing_nonneg _
    (GaussianLinearFieldMatrixCoordinates.units_orthonormal.comp Subtype.val Subtype.val_injective) _ _

theorem square_covariance_lower_bound (f g : sector 2) :
    2 * (inner ℝ f.val g.val)^2 ≤
      inner ℝ (square f) (square g) - ‖f.val‖^2 * ‖g.val‖^2 := by
  rw [covariance_polarization]
  have hp := completed_contraction_pairing_nonneg f g
  nlinarith [sq_nonneg ‖projection 2 (product f g)‖]

theorem squares_nonnegatively_correlated (f g : sector 2) :
    ‖f.val‖^2 * ‖g.val‖^2 ≤ inner ℝ (square f) (square g) := by
  have h := square_covariance_lower_bound f g
  nlinarith [sq_nonneg (inner ℝ f.val g.val)]
theorem cross_fourth_integrable (f g : sector 2) :
    Integrable (fun ω => (f.val ω)^2 * (g.val ω)^2) gaussianProduct := by
  have hi := (Lp.memLp (square f)).integrable_mul (Lp.memLp (square g))
  apply hi.congr
  filter_upwards [square_coeFn f, square_coeFn g] with ω hf hg
  simp only [Pi.mul_apply, hf, hg]

theorem square_inner_integral (f g : sector 2) :
    inner ℝ (square f) (square g) =
      ∫ ω, (f.val ω)^2 * (g.val ω)^2 ∂gaussianProduct := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [square_coeFn f, square_coeFn g] with ω hf hg
  simp only [hf, hg, Real.inner_apply]

theorem cross_fourth_lower_bound (f g : sector 2) :
    ‖f.val‖^2 * ‖g.val‖^2 + 2 * (inner ℝ f.val g.val)^2 ≤
      ∫ ω, (f.val ω)^2 * (g.val ω)^2 ∂gaussianProduct := by
  rw [← square_inner_integral]
  linarith [square_covariance_lower_bound f g]
end OperatorDerivativeRewrite.Foundation.GaussianQuadraticSquareCovariance
