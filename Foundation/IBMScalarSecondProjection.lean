import Foundation.IBMQuarticLiteralJoint
import Foundation.GaussianTerminalPredictionSpectrum

/-! An unnormalized single-observation projection and the genuine second
source sector of bounded C2 Gaussian compositions. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.IBMScalarSecondProjection
open InfiniteGaussian GaussianTimeSpaceHermite GaussianNumberSectors
open GaussianSingleObservationPrediction GaussianTerminalPredictionSpectrum
open IBMFirstChaosMixedStein IBMFirstChaosDiagonalStein

def varianceRankProjection (u : CoefficientSpace) (n : ℕ) : GaussianL2 →L[ℝ] GaussianL2 :=
  ((n.factorial : ℝ)*(‖u‖^2)^n)⁻¹ •
    (innerSL ℝ (wick u n : GaussianL2)).smulRight (wick u n : GaussianL2)

theorem varianceRankProjection_apply (u : CoefficientSpace) (n : ℕ) (f : GaussianL2) :
    varianceRankProjection u n f =
      (inner ℝ (wick u n : GaussianL2) f/((n.factorial : ℝ)*(‖u‖^2)^n)) •
        (wick u n : GaussianL2) := by
  simp [varianceRankProjection, div_eq_mul_inv, smul_smul, mul_comm]

/-- Reuse the verified Wick density without imposing unit variance. -/
theorem terminal_projection_unnormalized (u : CoefficientSpace) (hu : u ≠ 0)
    (f : GaussianL2) (hf : f ∈ singleGenerated u) (n : ℕ) :
    projection n f = (inner ℝ (wick u n : GaussianL2) f/((n.factorial : ℝ)*(‖u‖^2)^n)) •
      (wick u n : GaussianL2) := by
  let L := projection n-varianceRankProjection u n
  have hs : wickSpan u ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨m,rfl⟩
    change projection n (wick u m : GaussianL2)-varianceRankProjection u n (wick u m : GaussianL2)=0
    rw [projection_wick, varianceRankProjection_apply, wick_inner, real_inner_self_eq_norm_sq]
    by_cases hn : n=m
    · subst m
      have hd : (n.factorial : ℝ)*(‖u‖^2)^n ≠ 0 :=
        mul_ne_zero (by positivity) (pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hu)))
      simp [hd]
    · simp [hn]
  have hc := (wickSpan u).topologicalClosure_minimal hs L.isClosed_ker
  rw [wickSpan_closure] at hc
  have he := hc hf
  change projection n f-varianceRankProjection u n f=0 at he
  rw [varianceRankProjection_apply] at he
  exact sub_eq_zero.mp he

theorem wick_two_zero : (wick (0 : CoefficientSpace) 2 : GaussianL2) = 0 := by
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  simpa using GaussianWickContinuity.wick_norm_sq (0 : CoefficientSpace) 2

theorem testClass_zero {φ : ℝ → ℝ} (hc : Continuous φ) {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    testClass (0 : CoefficientSpace) hc hA = φ 0 • gaussianOne := by
  apply Lp.ext
  filter_upwards [testClass_coeFn (0 : CoefficientSpace) hc hA,
    Lp.coeFn_smul (φ 0) gaussianOne, gaussianOne_coeFn] with ω ht hs ho
  rw [ht, hs, Pi.smul_apply, ho]
  simp

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) {A B C : ℝ}
  (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖deriv φ x‖ ≤ B)
  (hC : ∀ x, ‖deriv (deriv φ) x‖ ≤ C)

include hφ hA hB hC in
/-- Actual second-sector reconstruction for nonlinear bounded C2 tests,
including the degenerate observation. No six-channel product is assumed. -/
theorem testClass_projection_two (u : CoefficientSpace) :
    projection 2 (testClass u hφ.continuous hA) =
      ((1/2 : ℝ)*(∫ ω, deriv (deriv φ) (firstChaosEmbedding u ω) ∂gaussianProduct)) •
        (wick u 2 : GaussianL2) := by
  by_cases hu : u = 0
  · subst u
    have hp : projection 2 gaussianOne = 0 := by
      have hz : (wick (0 : CoefficientSpace) 0 : GaussianL2) = gaussianOne := core_zero _ _
      simpa [hz] using
        projection_wick (0 : CoefficientSpace) 2 0
    rw [testClass_zero, map_smul, hp, smul_zero, wick_two_zero, smul_zero]
  · rw [terminal_projection_unnormalized u hu _ (testClass_generated u hφ.continuous hA) 2,
      second_pairing_integral, second_diagonal hφ hA hB hC]
    congr 1
    norm_num
    field_simp

/-- Direct specialization to the actual shifted Schwartz derivative
coefficients in the IBM correction. -/
theorem shiftedJet_projection_two (g : SchwartzMap ℝ ℝ) (a : ℝ) (k : ℕ) (u : CoefficientSpace) :
    projection 2 (testClass u (IBMCorrectionStein.shiftedJet_smooth g a k).continuous
      (IBMCorrectionStein.shiftedJet_bound g a k)) =
      ((1/2 : ℝ)*(∫ ω, IBMCorrectionStein.shiftedJet g a (k+2) (firstChaosEmbedding u ω)
        ∂gaussianProduct)) • (wick u 2 : GaussianL2) := by
  have hb : ∀ x, ‖deriv (IBMCorrectionStein.shiftedJet g a k) x‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (IBMCorrectionStein.jet g (k+1)) := by
    rw [IBMCorrectionStein.shiftedJet_deriv]
    exact IBMCorrectionStein.shiftedJet_bound g a (k+1)
  have hc : ∀ x, ‖deriv (deriv (IBMCorrectionStein.shiftedJet g a k)) x‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (IBMCorrectionStein.jet g (k+2)) := by
    rw [IBMCorrectionStein.shiftedJet_deriv, IBMCorrectionStein.shiftedJet_deriv]
    exact IBMCorrectionStein.shiftedJet_bound g a (k+2)
  simpa only [IBMCorrectionStein.shiftedJet_deriv] using
    testClass_projection_two (IBMCorrectionStein.shiftedJet_smooth g a k)
      (IBMCorrectionStein.shiftedJet_bound g a k) hb hc u

end OperatorDerivativeRewrite.Foundation.IBMScalarSecondProjection
