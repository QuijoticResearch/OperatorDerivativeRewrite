import Foundation.GaussianQuadraticProductSectors

/-! Exact degree 0/2/4 support for products of completed quadratic targets. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianSecondChaosProductDecomposition
open InfiniteGaussian GaussianNumberSectors GaussianTimeSpaceHermite
open GaussianSecondChaosL4 GaussianSecondChaosProduct GaussianSecondChaosFourthLower
open GaussianQuadraticProductSectors GaussianDiagonalQuadraticL4 GaussianFiniteQuadraticL4
open GaussianQuadraticSpectralTransport GaussianQuadraticMatrixApproximation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def residual : GaussianL2 →L[ℝ] GaussianL2 :=
  projection 0 + projection 2 + projection 4 - ContinuousLinearMap.id ℝ GaussianL2

def supported : Submodule ℝ GaussianL2 := residual.ker

theorem supported_isClosed : IsClosed (supported : Set GaussianL2) := residual.isClosed_ker

theorem mem_supported (q : GaussianL2) :
    q ∈ supported ↔ projection 0 q + projection 2 q + projection 4 q = q := by
  change residual q = 0 ↔ _
  simp only [residual, sub_apply, add_apply,
    ContinuousLinearMap.id_apply, sub_eq_zero]

theorem sector_mem_supported {n : ℕ} (hn : n = 0 ∨ n = 2 ∨ n = 4)
    {q : GaussianL2} (hq : q ∈ sector n) : q ∈ supported := by
  rw [mem_supported]
  have hp (k : ℕ) := projection_of_sector (n := k) (⟨q, hq⟩ : sector n)
  rcases hn with hn | hn | hn <;> subst n <;> simp_all

def wickTwo (u : CoefficientSpace) : sector 2 :=
  ⟨wick u 2, IBMCubicFirstChaos.wick_mem_sector u 2⟩

theorem wick_self_product_supported (u : CoefficientSpace) :
    product (wickTwo u) (wickTwo u) ∈ supported := by
  have he : product (wickTwo u) (wickTwo u) = GaussianPureQuadraticProduct.quadraticSquare u := by
    apply Lp.ext
    filter_upwards [product_coeFn (wickTwo u) (wickTwo u),
      GaussianPureQuadraticProduct.quadraticSquare_coeFn u] with ω hp hq
    rw [hp, hq]
    exact (pow_two _).symm
  rw [he, GaussianPureQuadraticProduct.quadraticSquare]
  apply supported.add_mem
  · apply supported.add_mem
    · exact sector_mem_supported (Or.inr (Or.inr rfl)) (IBMCubicFirstChaos.wick_mem_sector u 4)
    · exact supported.smul_mem _ (sector_mem_supported (Or.inr (Or.inl rfl))
        (IBMCubicFirstChaos.wick_mem_sector u 2))
  · exact supported.smul_mem _ (sector_mem_supported (Or.inl rfl)
      (IBMCubicFirstChaos.wick_mem_sector u 0))

theorem orthonormal_wick_products_supported {I : Type*} [Fintype I]
    (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (i j : I) :
    product (wickTwo (v i)) (wickTwo (v j)) ∈ supported := by
  classical
  by_cases hij : i = j
  · subst j; exact wick_self_product_supported _
  · let h : Fin 2 → CoefficientSpace := ![v i, v j]
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
    exact sector_mem_supported (Or.inr (Or.inr rfl)) (orthonormal_wick_product_mem_four h hh)

theorem diagonal_square_supported {I : Type*} [Fintype I]
    (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (a : I → ℝ) :
    (polynomialProduct (target v a) (target v a) : GaussianL2) ∈ supported := by
  classical
  let f : sector 2 := ⟨target v a, target_mem_second_chaos v a⟩
  have he : f = ∑ i, a i • wickTwo (v i) := by
    apply Subtype.ext
    simp only [f, target, Submodule.coe_sum, Submodule.coe_smul, wickTwo]
  rw [← square_polynomial _ (target_mem_second_chaos v a), ← product_self_eq_square]
  change productLinear f f ∈ supported
  rw [he]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
  apply supported.sum_mem
  intro i _
  apply supported.sum_mem
  intro j _
  exact supported.smul_mem _ (supported.smul_mem _ (orthonormal_wick_products_supported v hv j i))

theorem matrix_square_supported {I : Type*} [Fintype I] [DecidableEq I]
    (h : I → CoefficientSpace) (hh : Orthonormal ℝ h) (A : Matrix I I ℝ) :
    (polynomialProduct (matrixCore h A) (matrixCore h A) : GaussianL2) ∈ supported := by
  rw [← matrixCore_symmetrize h A, matrixCore_spectral (symmetrize_hermitian A)]
  exact diagonal_square_supported _ (rotatedSources_orthonormal h hh _) _

theorem square_supported (f : sector 2) : square f ∈ supported := by
  apply supported_isClosed.mem_of_tendsto (square_approximation_tendsto f)
  apply Eventually.of_forall
  intro n
  rw [show square (approximation f n) =
    (polynomialProduct
      (boxCore (Finset.range n) ⟨GaussianDivergenceRecovery.recovery f.val,
        GaussianQuadraticRecoverySurjectivity.recovery_second_chaos_linear f.property⟩)
      (boxCore (Finset.range n) ⟨GaussianDivergenceRecovery.recovery f.val,
        GaussianQuadraticRecoverySurjectivity.recovery_second_chaos_linear f.property⟩) : GaussianL2)
    from square_polynomial _ _]
  exact matrix_square_supported _
    (GaussianLinearFieldMatrixCoordinates.units_orthonormal.comp Subtype.val Subtype.val_injective) _

theorem product_supported (f g : sector 2) : product f g ∈ supported := by
  have he : product f g = (1/2 : ℝ) • (square (f+g) - square f - square g) := by
    simp only [← product_self_eq_square, product_add_left, product_add_right, product_comm g f]
    module
  rw [he]
  exact supported.smul_mem _ (supported.sub_mem
    (supported.sub_mem (square_supported (f+g)) (square_supported f)) (square_supported g))

theorem product_decomposition (f g : sector 2) :
    product f g = projection 0 (product f g) + projection 2 (product f g) +
      projection 4 (product f g) := ((mem_supported _).mp (product_supported f g)).symm

theorem product_projection_eq_zero (f g : sector 2) (n : ℕ)
    (h0 : n ≠ 0) (h2 : n ≠ 2) (h4 : n ≠ 4) : projection n (product f g) = 0 := by
  have he := product_decomposition f g
  have hp (k : ℕ) := projection_of_sector (n := n)
    (⟨projection k (product f g), projection_mem k _⟩ : sector k)
  calc
    projection n (product f g) = projection n
      (projection 0 (product f g) + projection 2 (product f g) + projection 4 (product f g)) :=
      congrArg (projection n) he
    _ = 0 := by simp only [map_add, hp, ite_eq_right h0, ite_eq_right h2, ite_eq_right h4, add_zero]

theorem product_projection_zero (f g : sector 2) :
    projection 0 (product f g) = inner ℝ f.val g.val • gaussianOne := by
  rw [projection_zero]
  congr 1
  rw [gaussianOne_inner_eq_integral, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [product_coeFn f g] with ω hp
  simp only [hp, RCLike.inner_apply, conj_trivial]
  ring

theorem product_energy_decomposition (f g : sector 2) :
    ‖product f g‖^2 = ‖projection 0 (product f g)‖^2 +
      ‖projection 2 (product f g)‖^2 + ‖projection 4 (product f g)‖^2 := by
  have ho (i j : ℕ) (hij : i ≠ j) :
      inner ℝ (projection i (product f g)) (projection j (product f g)) = 0 :=
    sectors_orthogonal hij ⟨_, projection_mem i _⟩ ⟨_, projection_mem j _⟩
  calc
    ‖product f g‖^2 = ‖projection 0 (product f g) + projection 2 (product f g) +
      projection 4 (product f g)‖^2 := congrArg (fun q : GaussianL2 => ‖q‖^2)
        (product_decomposition f g)
    _ = _ := by
      rw [norm_add_sq_real, norm_add_sq_real, inner_add_left,
        ho 0 2 (by decide), ho 0 4 (by decide), ho 2 4 (by decide)]
      ring
end OperatorDerivativeRewrite.Foundation.GaussianSecondChaosProductDecomposition
