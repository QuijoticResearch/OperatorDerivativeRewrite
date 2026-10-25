import Foundation.IBMActualQuarticSourceTesting

/-! Exact source-second-chaos projection for bounded C2 nonlinearities.
All bounds are explicit; zero Gaussian directions are included. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMBoundedC2SecondProjection
open InfiniteGaussian IBMFirstChaosMixedStein GaussianNumberSectors GaussianTimeSpaceHermite

def coefficient (φ : ℝ → ℝ) (u : CoefficientSpace) : ℝ :=
  (1/2:ℝ)*(∫ X, deriv (deriv φ) (firstChaosEmbedding u X) ∂gaussianProduct)

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) {A B C : ℝ}
  (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖deriv φ x‖ ≤ B)
  (hC : ∀ x, ‖deriv (deriv φ) x‖ ≤ C)

include hB hC in
theorem projection_two (u : CoefficientSpace) :
    projection 2 (testClass u hφ.continuous hA) =
      coefficient φ u • (wick u 2 : GaussianL2) := by
  apply IBMSecondChaosTesting.projection_eq_of_wick_tests
  · exact (sector 2).smul_mem _ (IBMCubicFirstChaos.wick_mem_sector u 2)
  · intro k
    have hs := second_centered_mixed hφ hA hB hC u k
    have he : inner ℝ (testClass u hφ.continuous hA) (wick k 2 : GaussianL2) =
        (inner ℝ u k)^2*(∫ X, deriv (deriv φ) (firstChaosEmbedding u X) ∂gaussianProduct) := by
      calc
        _ = inner ℝ (wick k 2 : GaussianL2) (testClass u hφ.continuous hA) := real_inner_comm _ _
        _ = _ := (second_pairing_integral u k hφ.continuous hA).trans hs
    rw [he,real_inner_smul_left,wick_inner]
    norm_num only [coefficient,ite_true,Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,
      Nat.cast_ofNat,Nat.cast_one]
    ring

include hB hC in
theorem second_pairing (f : GaussianL2) (hf : f ∈ sector 2) (u : CoefficientSpace) :
    inner ℝ f (testClass u hφ.continuous hA) =
      coefficient φ u*inner ℝ f (IBMSchwartzSourceContinuity.rawProduct u u) := by
  have hp := (sector 2).starProjection_inner_eq_zero (testClass u hφ.continuous hA) f hf
  change inner ℝ (testClass u hφ.continuous hA-
    projection 2 (testClass u hφ.continuous hA)) f = 0 at hp
  rw [inner_sub_left,projection_two hφ hA hB hC,real_inner_smul_left] at hp
  have hp' : inner ℝ f (testClass u hφ.continuous hA) =
      coefficient φ u*inner ℝ f (wick u 2 : GaussianL2) := by
    simpa only [real_inner_comm] using sub_eq_zero.mp hp
  have h0 : inner ℝ f gaussianOne = 0 := by
    have hg : gaussianOne ∈ sector 0 := by
      simpa only [wick,core_zero] using IBMCubicFirstChaos.wick_mem_sector u 0
    exact sectors_orthogonal (show (2:ℕ) ≠ 0 by decide) ⟨f,hf⟩ ⟨gaussianOne,hg⟩
  rw [IBMSourceProductBounds.rawProduct_eq_cross,inner_add_right,inner_smul_right,
    h0,mul_zero,add_zero,IBMQuarticSecondChaos.cross_self]
  exact hp'

include hC in
theorem coefficient_bound (u : CoefficientSpace) : ‖coefficient φ u‖ ≤ C/2 := by
  have hb : ‖∫ X, deriv (deriv φ) (firstChaosEmbedding u X) ∂gaussianProduct‖ ≤ C := by
    simpa using norm_integral_le_of_norm_le_const (μ := gaussianProduct)
      (Filter.Eventually.of_forall fun X => hC (firstChaosEmbedding u X))
  change ‖(1/2:ℝ)*(∫ X, deriv (deriv φ) (firstChaosEmbedding u X) ∂gaussianProduct)‖ ≤ _
  rw [norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  linarith

end OperatorDerivativeRewrite.Foundation.IBMBoundedC2SecondProjection
