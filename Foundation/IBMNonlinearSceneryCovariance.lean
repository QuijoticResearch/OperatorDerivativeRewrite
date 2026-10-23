import Foundation.GaussianCosineProductCovariance
import Foundation.IBMClockAverageCandidate

/-! Uniform nonlinear source covariance for the ACTUAL IBM mollifiers.
The four value/derivative bounds are discharged using physical Brownian
indicator kernels, positivity and unit mollifier mass. No closed clock-domain
or time-integration conclusion is inferred from this source estimate alone. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearSceneryCovariance
open InfiniteGaussian GaussianTimeHilbert IBMPhysicalNoiseVectors IBMPhysicalNoiseCalculus
open IBMPhysicalNoiseRealization IBMPhysicalDerivativeKernel IBMMollifier IBMFoldedTransitionBound
open IBMContinuousScenery IBMGaussianSteinMoments IBMJointMollifierGaussian
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable

theorem translated_vector_bound (m : ℕ) (q r : ℝ) :
    |inner ℝ (vector r) (translatedClass (kernel m) (kernel_smooth m).continuous
      (kernel_compactSupport m) q)| ≤ 1 := by
  rw [vector_inner_integral]
  change ‖∫ x in (0 : ℝ)..r, translatedClass (kernel m) (kernel_smooth m).continuous
    (kernel_compactSupport m) q x‖ ≤ 1
  calc
    _ ≤ ∫ x in uIoc (0 : ℝ) r,
        ‖translatedClass (kernel m) (kernel_smooth m).continuous (kernel_compactSupport m) q x‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ = ∫ x in uIoc (0 : ℝ) r, kernel m (q-x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (translatedClass_coeFn (kernel m)
        (kernel_smooth m).continuous (kernel_compactSupport m) q)] with x hx
      rw [hx,Real.norm_of_nonneg (kernel_nonneg m _)]
    _ ≤ ∫ x, kernel m (q-x) :=
      setIntegral_le_integral (shifted_integrable m q) (ae_of_all _ fun x => kernel_nonneg m _)
    _ = 1 := shifted_mass m q

theorem convolution_mixed_bound (n m : ℕ) (r q : ℝ) :
    |inner ℝ (convolutionKernel (kernel n) r) (convolutionKernel (deriv (kernel m)) q)| ≤ 1 := by
  rw [derivative_eq_translated ((kernel_smooth m).of_le (by norm_num)) (kernel_compactSupport m)]
  let d := translatedClass (kernel m) (kernel_smooth m).continuous (kernel_compactSupport m) q
  have hi := convolutionKernel_integrable (kernel_smooth n).continuous (kernel_compactSupport n) r
  have he : inner ℝ (convolutionKernel (kernel n) r) d =
      (innerSL ℝ d) (∫ x, kernel n (r-x) • vector x) := real_inner_comm _ _
  rw [he,← (innerSL ℝ d).integral_comp_comm hi]
  have hs := (innerSL ℝ d).integrable_comp hi
  calc
    _ ≤ ∫ x, ‖(innerSL ℝ d) (kernel n (r-x) • vector x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, kernel n (r-x) := by
      apply integral_mono hs.norm (shifted_integrable n r)
      intro x
      have hb : |inner ℝ d (vector x)| ≤ 1 := by
        simpa only [real_inner_comm] using translated_vector_bound m q x
      change |inner ℝ d (kernel n (r-x) • vector x)| ≤ kernel n (r-x)
      rw [inner_smul_right,abs_mul,abs_of_nonneg (kernel_nonneg n _)]
      exact (mul_le_mul_of_nonneg_left hb (kernel_nonneg n _)).trans_eq (mul_one _)
    _ = 1 := shifted_mass n r

theorem scenery_mixed_bound (n m : ℕ) (r q : ℝ) :
    |inner ℝ (wholeLineScenery (kernel n) r) (wholeLineScenery (deriv (kernel m)) q)| ≤ 1 := by
  rw [← convolutionKernel_realizes (kernel_smooth n).continuous (kernel_compactSupport n),
    ← convolutionKernel_realizes ((kernel_smooth m).continuous_deriv (by norm_num))
      (kernel_compactSupport m).deriv,physicalNoise.inner_map_map]
  exact convolution_mixed_bound n m r q

theorem coefficient_mixed_bound (n m : ℕ) (r q : ℝ) :
    |inner ℝ (tripleCoefficient n r 0) (tripleCoefficient m q 1)| ≤ 1 := by
  rw [← firstChaosEmbedding.inner_map_map,IBMOriginalBoundaryResidual.triple_embedding,
    IBMOriginalBoundaryResidual.triple_embedding]
  simpa [derivativeKernel] using scenery_mixed_bound n m r q

/-- Every cross-covariance premise is proved for the old actual source
directions. The correction is uniformly bounded while derivative variances
may diverge. This is an absolute EXPECTATION bound, not E of an absolute value. -/
theorem nonlinear_source_bound (n m : ℕ) (r q : ℝ) :
    |∫ ω, firstChaosEmbedding (tripleCoefficient n r 1) ω*
      firstChaosEmbedding (tripleCoefficient m q 1) ω*
        Real.cos (firstChaosEmbedding (tripleCoefficient n r 0) ω)*
          Real.cos (firstChaosEmbedding (tripleCoefficient m q 0) ω) ∂gaussianProduct| ≤
            overlap n m r q+4 := by
  have h := GaussianCosineProductCovariance.product_bound
    (tripleCoefficient n r 0) (tripleCoefficient m q 0)
    (tripleCoefficient n r 1) (tripleCoefficient m q 1) (C := 1) zero_le_one
      (coefficient_mixed_bound n n r r) (coefficient_mixed_bound m n q r)
      (coefficient_mixed_bound n m r q) (coefficient_mixed_bound m m q q)
  have he : inner ℝ (tripleCoefficient n r 1) (tripleCoefficient m q 1) = overlap n m r q := by
    simpa only [IBMClockAverageCandidate.sourceColumn,firstChaosEmbedding.inner_map_map] using
      IBMClockAverageCandidate.sourceColumn_inner n m r q
  simpa only [he,abs_of_nonneg (overlap_nonneg n m r q),one_pow,mul_one] using h

end OperatorDerivativeRewrite.Foundation.IBMNonlinearSceneryCovariance
