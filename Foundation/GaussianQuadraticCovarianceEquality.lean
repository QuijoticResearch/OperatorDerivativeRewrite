import Foundation.GaussianQuadraticSquareCovariance
import Mathlib.Probability.Independence.Integration

/-! Equality in quadratic square covariance and finite matrix annihilation. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticCovarianceEquality
open InfiniteGaussian GaussianNumberSectors GaussianSecondChaosL4 GaussianSecondChaosProduct
open GaussianQuadraticSquareCovariance GaussianQuadraticMatrixContraction GaussianQuadraticSourceHodge
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem square_covariance_eq_zero_iff (f g : sector 2) :
    inner ℝ (square f) (square g) = ‖f.val‖^2 * ‖g.val‖^2 ↔
      inner ℝ f.val g.val = 0 ∧
      inner ℝ (projection 2 (square f)) (projection 2 (square g)) = 0 ∧
      projection 2 (product f g) = 0 := by
  have he := covariance_polarization f g
  have hp := completed_contraction_pairing_nonneg f g
  constructor
  · intro hz
    have hc : (inner ℝ f.val g.val)^2 = 0 := by
      nlinarith [sq_nonneg ‖projection 2 (product f g)‖]
    have hn : ‖projection 2 (product f g)‖^2 = 0 := by nlinarith
    refine ⟨sq_eq_zero_iff.mp hc, ?_, norm_eq_zero.mp (sq_eq_zero_iff.mp hn)⟩
    linarith
  · rintro ⟨hc, hp, hn⟩
    rw [hc, hp, hn, norm_zero] at he
    norm_num at he
    linarith

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem hermitian_transpose {A : Matrix I I ℝ} (hA : A.IsHermitian) : A.transpose = A := by
  ext i j
  have he := congrArg (fun M : Matrix I I ℝ => M i j) hA
  simpa only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial] using he

theorem hermitian_square_frobenius_pair {A B : Matrix I I ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ i, ∑ j, (A*A) i j * (B*B) i j) = ∑ i, ∑ j, ((A*B) i j)^2 := by
  have he : Matrix.trace ((A*B).transpose * (A*B)) = Matrix.trace ((A*A)*(B*B)) := by
    rw [Matrix.transpose_mul, hermitian_transpose hA, hermitian_transpose hB]
    calc
      Matrix.trace ((B*A)*(A*B)) = Matrix.trace (B*((A*A)*B)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace (((A*A)*B)*B) := Matrix.trace_mul_comm _ _
      _ = _ := by rw [Matrix.mul_assoc]
  calc
    _ = Matrix.trace ((A*A)*(B*B)) := by
      rw [frobenius_pair_trace, Matrix.transpose_mul, hermitian_transpose hA]
    _ = Matrix.trace ((A*B).transpose * (A*B)) := he.symm
    _ = _ := by rw [← frobenius_pair_trace]; simp only [pow_two]

theorem matrix_contraction_pairing (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    {A B : Matrix I I ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    inner ℝ (projection 2 (square (matrixSectorMap h A)))
      (projection 2 (square (matrixSectorMap h B))) =
      32 * ∑ i, ∑ j, ((A*B) i j)^2 := by
  have hAA : (A*A).IsHermitian := by simpa only [pow_two] using hA.pow 2
  have hBB : (B*B).IsHermitian := by simpa only [pow_two] using hB.pow 2
  simp only [← product_self_eq_square,
    hermitian_product_self_projection h hh hA, hermitian_product_self_projection h hh hB]
  rw [real_inner_smul_left, real_inner_smul_right, hermitian_target_inner h hh hAA hBB,
    hermitian_square_frobenius_pair hA hB]
  ring

theorem frobenius_sq_zero_iff (M : Matrix I I ℝ) :
    (∑ i, ∑ j, (M i j)^2) = 0 ↔ M = 0 := by
  constructor
  · intro hz
    ext i j
    have hi := Finset.single_le_sum (s := Finset.univ)
      (fun k _ => show 0 ≤ ∑ l, (M k l)^2 by positivity) (Finset.mem_univ i)
    have hj := Finset.single_le_sum (s := Finset.univ)
      (fun l _ => sq_nonneg (M i l)) (Finset.mem_univ j)
    have he : (M i j)^2 = 0 := by nlinarith [hj.trans hi]
    exact sq_eq_zero_iff.mp he
  · intro hz
    simp only [hz, Matrix.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]

theorem matrix_square_covariance_zero_iff (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    {A B : Matrix I I ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    inner ℝ (square (matrixSectorMap h A)) (square (matrixSectorMap h B)) =
      ‖(matrixSectorMap h A).val‖^2 * ‖(matrixSectorMap h B).val‖^2 ↔ A*B = 0 := by
  rw [square_covariance_eq_zero_iff]
  constructor
  · rintro ⟨_, hp, _⟩
    rw [matrix_contraction_pairing h hh hA hB] at hp
    apply (frobenius_sq_zero_iff (A*B)).mp
    linarith
  · intro hab
    have hba : B*A = 0 := by
      have he := congrArg Matrix.transpose hab
      simpa only [Matrix.transpose_mul, hermitian_transpose hA, hermitian_transpose hB,
        Matrix.transpose_zero] using he
    refine ⟨?_, ?_, ?_⟩
    · change inner ℝ (quadraticTarget h A) (quadraticTarget h B) = 0
      rw [hermitian_target_inner h hh hA hB, frobenius_pair_trace,
        hermitian_transpose hA, hab, Matrix.trace_zero, mul_zero]
    · rw [matrix_contraction_pairing h hh hA hB, hab]
      simp
    · rw [hermitian_mixed_projection_two h hh hA hB, hab, hba, zero_add]
      change (2 : ℝ) • GaussianFiniteQuadraticL4.matrixTargetMap h 0 = 0
      rw [map_zero, smul_zero]

theorem independent_squares_factorize (f g : sector 2)
    (hfg : ProbabilityTheory.IndepFun f.val g.val gaussianProduct) :
    inner ℝ (square f) (square g) = ‖f.val‖^2 * ‖g.val‖^2 := by
  have hm : Measurable (fun x : ℝ => x^2) := by fun_prop
  have hs := hfg.comp hm hm
  have he := hs.integral_mul_eq_mul_integral
    ((Lp.aestronglyMeasurable f.val).pow 2) ((Lp.aestronglyMeasurable g.val).pow 2)
  have hn (u : GaussianL2) : (∫ ω, (u ω)^2 ∂gaussianProduct) = ‖u‖^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (BochnerL2Dominated.norm_sq_integral u).symm
  rw [square_inner_integral]
  change (∫ ω, (f.val ω)^2 * (g.val ω)^2 ∂gaussianProduct) = _
  simpa only [Pi.mul_apply, Function.comp_def, hn] using he

theorem matrix_independent_implies_mul_zero (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    {A B : Matrix I I ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hind : ProbabilityTheory.IndepFun (matrixSectorMap h A).val (matrixSectorMap h B).val gaussianProduct) :
    A*B = 0 := by
  apply (matrix_square_covariance_zero_iff h hh hA hB).mp
  exact independent_squares_factorize _ _ hind
end OperatorDerivativeRewrite.Foundation.GaussianQuadraticCovarianceEquality
