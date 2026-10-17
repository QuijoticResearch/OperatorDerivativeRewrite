import Foundation.GaussianSecondChaosProductDecomposition

/-! Degree-two contractions of finite quadratic squares, and exact completed
fourth cumulants obtained by strong square approximation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticContraction
open InfiniteGaussian GaussianNumberSectors GaussianTimeSpaceHermite
open GaussianSecondChaosL4 GaussianSecondChaosProduct GaussianSecondChaosFourthLower
open GaussianSecondChaosProductDecomposition GaussianQuadraticProductSectors
open GaussianDiagonalQuadraticL4 GaussianFiniteQuadraticL4 GaussianQuadraticSpectralTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem wick_self_product (u : CoefficientSpace) :
    product (wickTwo u) (wickTwo u) = GaussianPureQuadraticProduct.quadraticSquare u := by
  apply Lp.ext
  filter_upwards [product_coeFn (wickTwo u) (wickTwo u),
    GaussianPureQuadraticProduct.quadraticSquare_coeFn u] with ω hp hq
  rw [hp, hq]
  exact (pow_two _).symm

theorem projection_two_wick_self (u : CoefficientSpace) :
    projection 2 (product (wickTwo u) (wickTwo u)) =
      (4*‖u‖^2 : ℝ) • (wick u 2 : GaussianL2) := by
  have hp (k : ℕ) := projection_of_sector (n := 2)
    (⟨(wick u k : GaussianL2), IBMCubicFirstChaos.wick_mem_sector u k⟩ : sector k)
  rw [wick_self_product, GaussianPureQuadraticProduct.quadraticSquare]
  simp only [map_add, map_smul, hp]
  norm_num

theorem orthonormal_wick_product_mem_four_of_ne {I : Type*} [Fintype I]
    (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (i j : I) (hij : i ≠ j) :
    product (wickTwo (v i)) (wickTwo (v j)) ∈ sector 4 := by
  classical
  let h : Fin 2 → CoefficientSpace := ![v i, v j]
  have hh : Orthonormal ℝ h := by
    rw [orthonormal_iff_ite]
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [h, orthonormal_iff_ite.mp hv, hij, Ne.symm hij, hv.norm_eq_one]
  have he : product (wickTwo (v i)) (wickTwo (v j)) =
      (polynomialProduct (wick (h 0) 2) (wick (h 1) 2) : GaussianL2) := by
    apply Lp.ext
    filter_upwards [product_coeFn (wickTwo (v i)) (wickTwo (v j)),
      polynomialProductL2_coeFn (wick (h 0) 2) (wick (h 1) 2)] with ω hp hq
    change product (wickTwo (v i)) (wickTwo (v j)) ω =
      polynomialProductL2 (wick (h 0) 2) (wick (h 1) 2) ω
    rw [hp, hq]
    rfl
  rw [he]
  exact orthonormal_wick_product_mem_four h hh

theorem projection_two_orthonormal_wick_product {I : Type*} [Fintype I] [DecidableEq I]
    (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (i j : I) :
    projection 2 (product (wickTwo (v i)) (wickTwo (v j))) =
      if i = j then (4 : ℝ) • (wick (v i) 2 : GaussianL2) else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [ite_true, projection_two_wick_self, hv.norm_eq_one, one_pow, mul_one]
  · rw [ite_eq_right hij]
    exact projection_of_sector (n := 2)
      (⟨_, orthonormal_wick_product_mem_four_of_ne v hv i j hij⟩ : sector 4)

theorem diagonal_square_projection_two {I : Type*} [Fintype I]
    (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (a : I → ℝ) :
    projection 2 (polynomialProduct (target v a) (target v a) : GaussianL2) =
      (4 : ℝ) • (target v (fun i => (a i)^2) : GaussianL2) := by
  classical
  let f : sector 2 := ⟨target v a, target_mem_second_chaos v a⟩
  have he : f = ∑ i, a i • wickTwo (v i) := by
    apply Subtype.ext
    simp only [f, target, Submodule.coe_sum, Submodule.coe_smul, wickTwo]
  rw [← square_polynomial _ (target_mem_second_chaos v a), ← product_self_eq_square]
  change projection 2 (productLinear f f) = _
  rw [he]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum]
  change (∑ j, ∑ i, a j • a i • projection 2 (product (wickTwo (v i)) (wickTwo (v j)))) = _
  simp only [projection_two_orthonormal_wick_product v hv, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [target, Submodule.coe_sum, Submodule.coe_smul, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

theorem diagonal_square_projection_two_energy {I : Type*} [Fintype I]
    (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (a : I → ℝ) :
    ‖projection 2 (polynomialProduct (target v a) (target v a) : GaussianL2)‖^2 =
      32 * ∑ i, (a i)^4 := by
  rw [diagonal_square_projection_two v hv, norm_smul, mul_pow, target_variance v hv]
  norm_num only [Real.norm_eq_abs, sq_abs]
  simp only [← pow_mul]
  norm_num
  ring

theorem diagonal_fourth_cumulant {I : Type*} [Fintype I]
    (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (a : I → ℝ) :
    ‖(polynomialProduct (target v a) (target v a) : GaussianL2)‖^2 -
      3 * (‖(target v a : GaussianL2)‖^2)^2 =
      (3/2 : ℝ) * ‖projection 2
        (polynomialProduct (target v a) (target v a) : GaussianL2)‖^2 := by
  rw [target_fourth_moment v hv, target_variance v hv,
    diagonal_square_projection_two_energy v hv]
  ring

theorem matrix_fourth_cumulant {I : Type*} [Fintype I] [DecidableEq I]
    (h : I → CoefficientSpace) (hh : Orthonormal ℝ h) (A : Matrix I I ℝ) :
    ‖(polynomialProduct (matrixCore h A) (matrixCore h A) : GaussianL2)‖^2 -
      3 * (‖(matrixCore h A : GaussianL2)‖^2)^2 =
      (3/2 : ℝ) * ‖projection 2
        (polynomialProduct (matrixCore h A) (matrixCore h A) : GaussianL2)‖^2 := by
  rw [← matrixCore_symmetrize h A, matrixCore_spectral (symmetrize_hermitian A)]
  exact diagonal_fourth_cumulant _ (rotatedSources_orthonormal h hh _) _

theorem completed_fourth_cumulant (f : sector 2) :
    ‖square f‖^2 - 3 * (‖f.val‖^2)^2 =
      (3/2 : ℝ) * ‖projection 2 (square f)‖^2 := by
  have hb := (tendsto_subtype_rng.mp (approximation_tendsto f)).norm
  have hs := square_approximation_tendsto f
  have hp := (projection 2).continuous.continuousAt.tendsto.comp hs
  have he (n : ℕ) : ‖square (approximation f n)‖^2 -
      3 * (‖(approximation f n).val‖^2)^2 =
        (3/2 : ℝ) * ‖projection 2 (square (approximation f n))‖^2 := by
    rw [show square (approximation f n) =
      (polynomialProduct
        (GaussianQuadraticMatrixApproximation.boxCore (Finset.range n)
          ⟨GaussianDivergenceRecovery.recovery f.val,
            GaussianQuadraticRecoverySurjectivity.recovery_second_chaos_linear f.property⟩)
        (GaussianQuadraticMatrixApproximation.boxCore (Finset.range n)
          ⟨GaussianDivergenceRecovery.recovery f.val,
            GaussianQuadraticRecoverySurjectivity.recovery_second_chaos_linear f.property⟩) : GaussianL2)
      from square_polynomial _ _]
    exact matrix_fourth_cumulant _
      (GaussianLinearFieldMatrixCoordinates.units_orthonormal.comp Subtype.val Subtype.val_injective) _
  have hl := (hs.norm.pow 2).sub ((tendsto_const_nhds (x := (3 : ℝ))).mul ((hb.pow 2).pow 2))
  have hr := (tendsto_const_nhds (x := (3/2 : ℝ))).mul (hp.norm.pow 2)
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

theorem completed_fourth_moment (f : sector 2) :
    (∫ ω, (f.val ω)^4 ∂gaussianProduct) = 3 * (‖f.val‖^2)^2 +
      (3/2 : ℝ) * ‖projection 2 (square f)‖^2 := by
  have he : (∫ ω, (f.val ω)^4 ∂gaussianProduct) = ‖square f‖^2 := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [square_coeFn f] with ω hq
    rw [Real.norm_eq_abs, sq_abs, hq]
    ring
  rw [he]
  linarith [completed_fourth_cumulant f]

theorem completed_fourth_projection_energy (f : sector 2) :
    ‖projection 4 (square f)‖^2 = 2 * (‖f.val‖^2)^2 +
      (1/2 : ℝ) * ‖projection 2 (square f)‖^2 := by
  have he := product_energy_decomposition f f
  rw [product_self_eq_square] at he
  have h0 := product_projection_zero f f
  rw [product_self_eq_square, real_inner_self_eq_norm_sq] at h0
  have hn0 : ‖projection 0 (square f)‖^2 = (‖f.val‖^2)^2 := by
    rw [h0, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      ← real_inner_self_eq_norm_sq gaussianOne,
      GaussianDeterministicGraphCore.gaussianOne_inner_self, mul_one]
  rw [hn0] at he
  linarith [completed_fourth_cumulant f]
theorem projection_two_square_energy_bound (f : sector 2) :
    ‖projection 2 (square f)‖^2 ≤ 8 * (‖f.val‖^2)^2 := by
  linarith [completed_fourth_cumulant f, square_norm_bound f]

theorem projection_four_square_energy_bounds (f : sector 2) :
    2 * (‖f.val‖^2)^2 ≤ ‖projection 4 (square f)‖^2 ∧
      ‖projection 4 (square f)‖^2 ≤ 6 * (‖f.val‖^2)^2 := by
  have he := completed_fourth_projection_energy f
  have hb := projection_two_square_energy_bound f
  constructor <;> nlinarith [sq_nonneg ‖projection 2 (square f)‖]

theorem gaussian_fourth_value_iff (f : sector 2) :
    ‖square f‖^2 = 3 * (‖f.val‖^2)^2 ↔ projection 2 (square f) = 0 := by
  have hc := completed_fourth_cumulant f
  constructor
  · intro he
    have hn : ‖projection 2 (square f)‖^2 = 0 := by linarith
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  · intro he
    rw [he, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at hc
    linarith
end OperatorDerivativeRewrite.Foundation.GaussianQuadraticContraction
