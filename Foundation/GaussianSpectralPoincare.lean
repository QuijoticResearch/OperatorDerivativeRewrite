import Foundation.GaussianChaosGraphConvergence

/-! The Gaussian Poincare estimate on the actual infinite-dimensional closed
derivative domain, derived from the proved all-order spectral energy identity. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianNumberSectors
open InfiniteGaussian

theorem gaussian_poincare_sq {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f, g) ∈ closedCylindricalDerivative.graph) :
    ‖f - inner ℝ gaussianOne f • gaussianOne‖ ^ 2 ≤ ‖g‖ ^ 2 := by
  have hd := (hasSum_ite_eq (0 : ℕ) (‖projection 0 f‖ ^ 2)).add (derivative_energy_hasSum hf)
  have hle : ‖f‖ ^ 2 ≤ ‖projection 0 f‖ ^ 2 + ‖g‖ ^ 2 := by
    apply hasSum_le _ (projection_hasSum_norm_sq f) hd
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ↓reduceIte, zero_add]
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      nlinarith [sq_nonneg ‖projection n f‖]
  have hp := (sector 0).inner_orthogonalProjectionOnto_eq_of_mem_right
    ((sector 0).orthogonalProjectionOnto f) f
  change inner ℝ (projection 0 f) (projection 0 f) = inner ℝ f (projection 0 f) at hp
  rw [real_inner_self_eq_norm_sq] at hp
  rw [← projection_zero f, norm_sub_sq_real, ← hp]
  linarith

theorem gaussian_poincare {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f, g) ∈ closedCylindricalDerivative.graph) :
    ‖f - inner ℝ gaussianOne f • gaussianOne‖ ≤ ‖g‖ := by
  have h := gaussian_poincare_sq hf
  nlinarith [norm_nonneg (f - inner ℝ gaussianOne f • gaussianOne), norm_nonneg g]

end OperatorDerivativeRewrite.Foundation.GaussianNumberSectors
