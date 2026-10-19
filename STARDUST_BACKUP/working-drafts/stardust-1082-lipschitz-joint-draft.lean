import Foundation.GaussianC2Ito
import Foundation.BrownianSignIntegral
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianLipschitzIntegrands
open GaussianContinuousIntegrands BrownianClockWeightedEnergy IBMConstructedSources
open GaussianProductDerivative
example {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (T : ℝ≥0) :
    (integrand hφ T : TimeProbabilityL2) =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (fun z => φ (sigma z)) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (Lp.stronglyMeasurable _).measurable
    ((hφ.continuous.measurable.comp sigma_measurable).indicator
      (PredictableRealL2.horizon_measurable T)))).mpr
  filter_upwards [integrand_slices hφ T,
    scalarCurry_coeFn (integrand hφ T : TimeProbabilityL2)] with t ht hc
  by_cases hp : t ∈ Ioc 0 (T : ℝ)
  · rw [indicator_of_mem hp] at ht
    filter_upwards [hc, clockPath_coordinate_ae t.toNNReal,
      valueL2_coeFn hφ t.toNNReal] with ω hc hw hv
    rw [← hc, ht, hv]
    simp [PredictableRealL2.horizon, hp, sigma, hw]
  · rw [indicator_of_notMem hp] at ht
    filter_upwards [hc, Lp.coeFn_zero ℝ 2 gaussianProduct] with ω hc hz
    rw [← hc, ht, hz]
    simp [PredictableRealL2.horizon, hp]
