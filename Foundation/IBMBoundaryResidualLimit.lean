import Foundation.IBMBoundaryLayerRemainder

/-! Strong L² closure of the two actual averaged boundary coefficient
terms. Identification with the manuscript's full correction still requires
the general Gaussian Stein identity; it is not assumed here. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMBoundaryResidualLimit
open InfiniteGaussian IBMConstructedSources IBMMollifier IBMContinuousScenery
open IBMBoundaryAveragedCoefficient IBMBoundaryLayerRemainder IBMBoundaryWeightedClock
variable {φ₂ φ₄ : ℝ → ℝ} {K₂ K₄ : ℝ≥0}
  (h₂ : LipschitzWith K₂ φ₂) (h₄ : LipschitzWith K₄ φ₄)

def coefficient (n : ℕ) (r : ℝ) : ℝ :=
  kernel n r * sourceAverage h₂ n r + residual h₄ n r

theorem coefficient_continuous (n : ℕ) : Continuous (coefficient h₂ h₄ n) :=
  ((kernel_smooth n).continuous.mul (sourceAverage_continuous h₂ n)).add
    (residual_continuous h₄ n)

/-- Both scalar terms are literal expectations of the existing scenery.
The covariance coefficient is derived from the actual variance derivative. -/
theorem coefficient_eq_covariance (n : ℕ) (r : ℝ) :
    coefficient h₂ h₄ n r =
      ((inner ℝ (wholeLineScenery (kernel n) r)
        (wholeLineScenery (deriv (kernel n)) r))^2 - 1/4) *
          (∫ ω, φ₄ (wholeLineScenery (kernel n) r ω) ∂gaussianProduct) +
      kernel n r * (∫ ω, φ₂ (wholeLineScenery (kernel n) r ω) ∂gaussianProduct) := by
  rw [coefficient, IBMBoundaryLayerRemainder.residual, slopeFactor,
    IBMVarianceClockGeometry.variance,
    wholeLineVariance_deriv (kernel n) (kernel_compactSupport n)
      ((kernel_smooth n).of_le (by norm_num)) r,
    sourceAverage_eq_integral, sourceAverage_eq_integral]
  ring

def pathIntegral (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) : ℝ :=
  ∫ t in 0..(T : ℝ), coefficient h₂ h₄ n |clockPath ω t.toNNReal|

theorem pathIntegral_decomposition (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) :
    pathIntegral h₂ h₄ n T ω = weightedPath h₂ n T ω +
      IBMBoundaryLayerRemainder.pathIntegral h₄ n T ω := by
  have hc := continuous_abs.comp ((clockPath ω).continuous.comp continuous_real_toNNReal)
  have hfirst := ((kernel_smooth n).continuous.comp hc).mul
    ((sourceAverage_continuous h₂ n).comp hc)
  exact intervalIntegral.integral_add (hfirst.intervalIntegrable 0 T)
    ((integrand_continuous h₄ n ω).intervalIntegrable 0 T)

def residualClass {M : ℝ} (hM : ∀ x, ‖φ₄ x‖ ≤ M) (n : ℕ) (T : ℝ≥0) : GaussianL2 :=
  weightedClass h₂ n T + integralClass h₄ hM n T

theorem residualClass_coeFn {M : ℝ} (hM : ∀ x, ‖φ₄ x‖ ≤ M) (n : ℕ) (T : ℝ≥0) :
    residualClass h₂ h₄ hM n T =ᵐ[gaussianProduct] pathIntegral h₂ h₄ n T := by
  filter_upwards [Lp.coeFn_add (weightedClass h₂ n T) (integralClass h₄ hM n T),
    weightedClass_coeFn h₂ n T, integralClass_coeFn h₄ hM n T] with ω ha hw hr
  rw [residualClass, ha, Pi.add_apply, hw, hr, pathIntegral_decomposition]

theorem residualClass_tendsto {M : ℝ} (hM : ∀ x, ‖φ₄ x‖ ≤ M) (T : ℝ≥0) :
    Tendsto (fun n => residualClass h₂ h₄ hM n T) atTop
      (𝓝 (φ₂ 0 • BrownianTanakaResidual.mass T)) := by
  have h := (weightedClass_tendsto h₂ T).add (integralClass_tendsto h₄ hM T)
  simpa only [residualClass, add_zero] using h

theorem pathIntegral_memLp {M : ℝ} (hM : ∀ x, ‖φ₄ x‖ ≤ M) (n : ℕ) (T : ℝ≥0) :
    MemLp (pathIntegral h₂ h₄ n T) 2 gaussianProduct :=
  (Lp.memLp (residualClass h₂ h₄ hM n T)).ae_eq (residualClass_coeFn h₂ h₄ hM n T)

theorem pathIntegral_tendsto {M : ℝ} (hM : ∀ x, ‖φ₄ x‖ ≤ M) (T : ℝ≥0) :
    Tendsto (fun n => (pathIntegral_memLp h₂ h₄ hM n T).toLp _) atTop
      (𝓝 (φ₂ 0 • BrownianMassLimitIdentification.coordinateClass T)) := by
  have he (n : ℕ) : (pathIntegral_memLp h₂ h₄ hM n T).toLp _ = residualClass h₂ h₄ hM n T := by
    apply Lp.ext
    exact (pathIntegral_memLp h₂ h₄ hM n T).coeFn_toLp.trans
      (residualClass_coeFn h₂ h₄ hM n T).symm
  simpa only [he, BrownianMassLimitIdentification.coordinateClass_eq] using
    residualClass_tendsto h₂ h₄ hM T

theorem schwartz_bound (g : SchwartzMap ℝ ℝ) (x : ℝ) :
    ‖g x‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
  simpa only [pow_zero, one_mul, iteratedDeriv_zero] using
    SchwartzMap.le_seminorm' ℝ 0 0 g x

theorem schwartz_residual_limit (g₂ g₄ : SchwartzMap ℝ ℝ) (T : ℝ≥0) :
    Tendsto (fun n => residualClass (schwartz_lipschitz g₂) (schwartz_lipschitz g₄)
      (schwartz_bound g₄) n T) atTop (𝓝 (g₂ 0 • BrownianTanakaResidual.mass T)) :=
  residualClass_tendsto (schwartz_lipschitz g₂) (schwartz_lipschitz g₄) (schwartz_bound g₄) T

end OperatorDerivativeRewrite.Foundation.IBMBoundaryResidualLimit
