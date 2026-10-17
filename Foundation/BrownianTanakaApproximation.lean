import Foundation.SmoothAbsoluteApproximation
import Foundation.BrownianSignIntegral

/-! Actual L2 convergence of smooth absolute-value terminal values and
their predictable stochastic coefficients. No local-time properties assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianTanakaApproximation
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianPredictableFull GaussianLipschitzIntegrands GaussianBoundedApproximation
open SmoothAbsoluteApproximation BrownianClockWeightedEnergy IBMConstructedSources
open RealSteklovApprox

theorem slope_tendsto_sign (x : ℝ) :
    Tendsto (fun n => slope (width n) x) atTop (𝓝 (BrownianSignIntegral.signum x)) := by
  by_cases hx : x = 0
  · simp only [hx, SmoothAbsoluteApproximation.slope, zero_div,
      BrownianSignIntegral.signum_zero]
    exact tendsto_const_nhds
  · have hw := width_tendsto.mono_right nhdsWithin_le_nhds
    have hr : Tendsto (fun n => radius (width n) x) atTop (𝓝 |x|) := by
      have ht := Real.continuous_sqrt.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := x ^ 2)).add (hw.pow 2))
      norm_num only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at ht
      rw [Real.sqrt_sq_eq_abs] at ht
      exact ht
    have h := (tendsto_const_nhds (x := x)).div hr (abs_ne_zero.mpr hx)
    have he : x / |x| = BrownianSignIntegral.signum x := by
      rcases lt_or_gt_of_ne hx with hn | hp
      · simp [BrownianSignIntegral.signum, hn, not_lt_of_gt hn, abs_of_neg hn, hx]
      · simp [BrownianSignIntegral.signum, hp, abs_of_pos hp, ne_of_gt hp]
    rw [he] at h
    exact h

theorem integrand_joint {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (T : ℝ≥0) :
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

theorem slope_sign_bound {e : ℝ} (he : 0 < e) (x : ℝ) :
    ‖slope e x‖ ≤ ‖BrownianSignIntegral.signum x‖ := by
  by_cases hx : x = 0
  · simp [hx, SmoothAbsoluteApproximation.slope, BrownianSignIntegral.signum_zero]
  · have hs : ‖BrownianSignIntegral.signum x‖ = 1 := by
      rcases lt_or_gt_of_ne hx with hn | hp
      · simp [BrownianSignIntegral.signum, hn, not_lt_of_gt hn]
      · simp [BrownianSignIntegral.signum, hp]
    rw [hs]
    exact slope_bound he x

def approximateField (n : ℕ) (T : ℝ≥0) : fullPredictable :=
  integrand (slopeLip (width_pos n)) T

theorem field_tendsto (T : ℝ≥0) :
    Tendsto (fun n => approximateField n T) atTop
      (𝓝 (BrownianSignIntegral.predictableField T)) := by
  apply tendsto_subtype_rng.mpr
  apply BochnerL2Dominated.tendsto_of_ae_norm_bound
  · intro n
    filter_upwards [integrand_joint (slopeLip (width_pos n)) T,
      BrownianSignIntegral.field_coeFn T] with z hn hs
    change ‖(integrand (slopeLip (width_pos n)) T : TimeProbabilityL2) z‖ ≤
      ‖BrownianSignIntegral.field T z‖
    rw [hn, hs]
    by_cases ht : z ∈ PredictableRealL2.horizon T
    · simpa only [indicator_of_mem ht] using slope_sign_bound (width_pos n) (sigma z)
    · simp [ht]
  · filter_upwards [ae_all_iff.mpr (fun n => integrand_joint (slopeLip (width_pos n)) T),
      BrownianSignIntegral.field_coeFn T] with z hn hs
    change Tendsto (fun n => (integrand (slopeLip (width_pos n)) T : TimeProbabilityL2) z)
      atTop (𝓝 (BrownianSignIntegral.field T z))
    simp only [hn, hs]
    by_cases ht : z ∈ PredictableRealL2.horizon T
    · simpa only [indicator_of_mem ht] using slope_tendsto_sign (sigma z)
    · simpa only [indicator_of_notMem ht] using (tendsto_const_nhds (x := (0 : ℝ)))

theorem integral_tendsto (T : ℝ≥0) :
    Tendsto (fun n => itoIntegral (approximateField n T)) atTop
      (𝓝 (BrownianSignIntegral.terminal T)) :=
  itoIntegral.continuous.continuousAt.tendsto.comp (field_tendsto T)

theorem absLip : LipschitzWith 1 (fun x : ℝ => |x|) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub x y

def absoluteValue (T : ℝ≥0) : GaussianL2 := valueL2 absLip T

theorem absoluteValue_coeFn (T : ℝ≥0) : absoluteValue T =ᵐ[gaussianProduct]
    fun ω => |clockPath ω T| := by
  filter_upwards [valueL2_coeFn absLip T, clockPath_coordinate_ae T] with ω hv hw
  exact hv.trans (congrArg abs hw.symm)

theorem terminal_tendsto (T : ℝ≥0) :
    Tendsto (fun n => valueL2 (functionLip (width_pos n)) T) atTop (𝓝 (absoluteValue T)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => value_uniform_error (functionLip (width_pos n)) absLip (width_pos n).le
      (uniform_error (width_pos n)) T)
  exact width_tendsto.mono_right nhdsWithin_le_nhds

end OperatorDerivativeRewrite.Foundation.BrownianTanakaApproximation
