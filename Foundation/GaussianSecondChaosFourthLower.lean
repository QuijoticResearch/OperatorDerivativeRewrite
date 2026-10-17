import Foundation.GaussianSecondChaosProduct

/-! Strong square approximation and the universal lower fourth-moment bound
for completed Gaussian second chaos. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace OperatorDerivativeRewrite.Foundation.GaussianSecondChaosFourthLower
open InfiniteGaussian GaussianNumberSectors GaussianDivergenceRecovery
open GaussianQuadraticRecoverySurjectivity GaussianLinearFieldDivergenceCompletion
open GaussianQuadraticMatrixApproximation GaussianSecondChaosL4 GaussianSecondChaosProduct
open GaussianLinearFieldMatrixCoordinates GaussianFiniteQuadraticL4

theorem boxCore_mem_second_chaos (s : Finset ℕ) (v : linearGaussianFields) :
    (boxCore s v : GaussianL2) ∈ sector 2 := by
  rw [boxCore_eq_divergence]
  exact completedDivergence_mem_sector_two (boxSource_mem s v)

def approximation (f : sector 2) (n : ℕ) : sector 2 :=
  ⟨boxCore (Finset.range n) ⟨recovery f.val, recovery_second_chaos_linear f.property⟩,
    boxCore_mem_second_chaos _ _⟩

theorem approximation_tendsto (f : sector 2) :
    Tendsto (approximation f) atTop (𝓝 f) := by
  apply tendsto_subtype_rng.mpr
  exact boxCore_tendsto f.val f.property

theorem square_approximation_tendsto (f : sector 2) :
    Tendsto (fun n => square (approximation f n)) atTop (𝓝 (square f)) := by
  simp only [← product_self_eq_square]
  exact product_continuous.continuousAt.tendsto.comp
    ((approximation_tendsto f).prodMk_nhds (approximation_tendsto f))

theorem square_norm_lower_bound (f : sector 2) :
    3 * (‖f.val‖^2)^2 ≤ ‖square f‖^2 := by
  have hl (n : ℕ) : 3 * (‖(approximation f n).val‖^2)^2 ≤
      ‖square (approximation f n)‖^2 := by
    rw [show square (approximation f n) =
      (polynomialProduct
        (boxCore (Finset.range n) ⟨recovery f.val, recovery_second_chaos_linear f.property⟩)
        (boxCore (Finset.range n) ⟨recovery f.val, recovery_second_chaos_linear f.property⟩) : GaussianL2)
      from square_polynomial _ _]
    exact finite_matrix_fourth_lower_bound _
      (units_orthonormal.comp Subtype.val Subtype.val_injective) _
  have ht := (boxCore_tendsto f.val f.property).norm
  have hs := (square_approximation_tendsto f).norm
  exact le_of_tendsto_of_tendsto (tendsto_const_nhds.mul ((ht.pow 2).pow 2))
    (hs.pow 2) (Eventually.of_forall hl)

theorem fourth_moment_lower_bound (f : sector 2) :
    3 * (‖f.val‖^2)^2 ≤ ∫ ω, (f.val ω)^4 ∂gaussianProduct := by
  have he : (∫ ω, (f.val ω)^4 ∂gaussianProduct) = ‖square f‖^2 := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [square_coeFn f] with ω hq
    rw [Real.norm_eq_abs, sq_abs, hq]
    ring
  rw [he]
  exact square_norm_lower_bound f

end OperatorDerivativeRewrite.Foundation.GaussianSecondChaosFourthLower
