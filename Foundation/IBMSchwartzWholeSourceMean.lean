import Foundation.IBMSchwartzLiteralJoint

/-! The actual source mean of the entire nonlinear correction. The origin
mean is proved zero by the actual boundary covariance symmetry. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzWholeSourceMean
open InfiniteGaussian IBMCorrectionStein IBMFirstChaosMixedStein IBMGaussianSteinMoments
open IBMSchwartzSecondProjection IBMSchwartzTimeProjection IBMSceneryAveragedCorrectionLimit

variable (g : SchwartzMap ℝ ℝ) (a : ℝ)

theorem origin_covariance_zero (n : ℕ) :
    inner ℝ (tripleCoefficient n 0 0) (tripleCoefficient n 0 1) = 0 := by
  rw [IBMOriginalBoundaryResidual.triple_inner]
  simpa [IBMJointMollifierGaussian.derivativeKernel] using
    IBMBoundaryCurvature.concrete_cross_covariance_zero n

theorem origin_inner_zero (n : ℕ) : inner ℝ gaussianOne (originClass g a n) = 0 := by
  rw [gaussianOne_inner_eq_integral]
  have he : (∫ ω, originClass g a n ω ∂gaussianProduct) =
      ∫ ω, firstChaosEmbedding (tripleCoefficient n 0 1) ω *
        shiftedJet g a 1 (firstChaosEmbedding (tripleCoefficient n 0 0) ω) ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [weightedClass_coeFn g a (tripleCoefficient n 0 0) 1
      (firstChaosEmbedding (tripleCoefficient n 0 1))] with ω hω
    change originClass g a n ω = _ at hω
    rw [hω]
    ring
  rw [he, shifted_first, origin_covariance_zero, zero_mul]

theorem mollified_mean (n : ℕ) (r : ℝ) :
    (∫ ω, mollifiedClass g a n r ω ∂gaussianProduct) =
      correction g a (tripleCoefficient n r 0) (tripleCoefficient n r 1) (tripleCoefficient n r 2) := by
  unfold correction
  apply integral_congr_ae
  exact correctionClass_coeFn g a _ _ _

/-- The actual whole source mean includes both stochastic terms. -/
theorem whole_source_mean (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) :
    inner ℝ gaussianOne (wholeCorrection g a n T ω) = (1/2 : ℝ)*averagedPath g a n T ω := by
  rw [wholeCorrection, inner_add_right, inner_smul_right, inner_smul_right,
    origin_inner_zero, mul_zero, zero_add]
  have hi := ((innerSL ℝ gaussianOne).intervalIntegral_comp_comm (μ := volume)
    ((mollified_path_continuous g a n ω).intervalIntegrable 0 T)).symm
  simp only [innerSL_apply_apply] at hi
  rw [hi]
  simp_rw [gaussianOne_inner_eq_integral, mollified_mean]
  rfl

theorem whole_projection_zero (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) :
    GaussianNumberSectors.projection 0 (wholeCorrection g a n T ω) =
      ((1/2 : ℝ)*averagedPath g a n T ω) • gaussianOne := by
  rw [GaussianNumberSectors.projection_zero, whole_source_mean]

end OperatorDerivativeRewrite.Foundation.IBMSchwartzWholeSourceMean
