import Foundation.IBMShiftedJetMoments

/-! Third/fourth source projections of actual shifted Schwartz tests,
including degenerate observations. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMHigherScalarProjection
open InfiniteGaussian GaussianTimeSpaceHermite GaussianNumberSectors
open IBMFirstChaosMixedStein IBMScalarSecondProjection IBMCorrectionStein IBMShiftedJetMoments

theorem value_three (x t : ℝ) : value 3 x t = x^3-3*t*x := by
  have he := value_recursion 1 x t
  norm_num [value_two, value_one] at he
  rw [he]
  ring

theorem third_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ) :
    inner ℝ (wick u 3 : GaussianL2)
      (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      ‖u‖^6*M g a u (j+3) 0 := by
  rw [L2_inner_eq_integral, ← centered_third g a u j]
  apply integral_congr_ae
  filter_upwards [core_coeFn u (‖u‖^2) 3,
    testClass_coeFn u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)] with ω hw ht
  change (wick u 3 : GaussianL2) ω = _ at hw
  rw [hw, ht]
  simp only [Real.inner_apply, value_three]

theorem fourth_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ) :
    inner ℝ (wick u 4 : GaussianL2)
      (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      ‖u‖^8*M g a u (j+4) 0 := by
  rw [L2_inner_eq_integral, ← centered_fourth g a u j]
  apply integral_congr_ae
  filter_upwards [core_coeFn u (‖u‖^2) 4,
    testClass_coeFn u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)] with ω hw ht
  change (wick u 4 : GaussianL2) ω = _ at hw
  rw [hw, ht]
  simp only [Real.inner_apply, GaussianQuarticWick.value_four] <;> ring

theorem wick_zero_positive (n : ℕ) (hn : 0 < n) : (wick (0 : CoefficientSpace) n : GaussianL2) = 0 := by
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  simpa [ne_of_gt hn] using GaussianWickContinuity.wick_norm_sq (0 : CoefficientSpace) n

theorem projection_of_pairing (u : CoefficientSpace) (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} (hc : Continuous φ) {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) (b : ℝ)
    (hp : inner ℝ (wick u n : GaussianL2) (testClass u hc hA) = (‖u‖ ^ 2) ^ n * b) :
    projection n (testClass u hc hA) = (b/(n.factorial : ℝ)) • (wick u n : GaussianL2) := by
  by_cases hu : u = 0
  · subst u
    have hg : projection n gaussianOne = 0 := by
      have hz : (wick (0 : CoefficientSpace) 0 : GaussianL2) = gaussianOne := core_zero _ _
      simpa [hz, ne_of_gt hn] using GaussianTerminalPredictionSpectrum.projection_wick (0 : CoefficientSpace) n 0
    rw [testClass_zero, map_smul, hg, smul_zero, wick_zero_positive n hn, smul_zero]
  · rw [terminal_projection_unnormalized u hu _ (testClass_generated u hc hA) n, hp]
    congr 1
    field_simp [norm_ne_zero_iff.mpr hu]

/-- Genuine source-three coefficient of the nonlinear Schwartz test. -/
theorem shiftedJet_projection_three (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ) :
    projection 3 (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      ((∫ ω, shiftedJet g a (j+3) (firstChaosEmbedding u ω) ∂gaussianProduct)/6) •
        (wick u 3 : GaussianL2) := by
  have hp := projection_of_pairing u 3 (by norm_num) (shiftedJet_smooth g a j).continuous
    (shiftedJet_bound g a j) (M g a u (j+3) 0) (by
      rw [third_pairing]
      ring)
  norm_num at hp
  simpa only [moment_zero] using hp

/-- Genuine source-four coefficient; j=2 retains the Q6 coefficient of
g'' needed for the mixed-product correction's fourth contraction channel. -/
theorem shiftedJet_projection_four (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ) :
    projection 4 (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      ((∫ ω, shiftedJet g a (j+4) (firstChaosEmbedding u ω) ∂gaussianProduct)/24) •
        (wick u 4 : GaussianL2) := by
  have hp := projection_of_pairing u 4 (by norm_num) (shiftedJet_smooth g a j).continuous
    (shiftedJet_bound g a j) (M g a u (j+4) 0) (by
      rw [fourth_pairing]
      ring)
  norm_num at hp
  simpa only [moment_zero] using hp

/-- A uniform native source-sector bound follows from the actual bounded
observable and projection contraction, without bounding its variance. -/
theorem bounded_projection_norm (u : CoefficientSpace) (n : ℕ) {φ : ℝ → ℝ}
    (hc : Continuous φ) {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    ‖projection n (testClass u hc hA)‖ ≤ A := by
  apply (projection_norm_le n _).trans
  apply GaussianBoundedApproximation.gaussian_norm_le ((norm_nonneg (φ 0)).trans (hA 0))
  filter_upwards [testClass_coeFn u hc hA] with ω hω
  rw [hω]
  exact hA _

end OperatorDerivativeRewrite.Foundation.IBMHigherScalarProjection
