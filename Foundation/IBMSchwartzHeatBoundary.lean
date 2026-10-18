import Foundation.IBMSchwartzHeatBounds

/-! Exact nonlinear Schwartz heat boundary accounting and decay of the
actual Gaussian-L2 endpoint. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatBoundary
open InfiniteGaussian IBMClockGaussianTail IBMClockHeatPotential IBMHeatTailDecay
open IBMQuarticHeatBoundary IBMSchwartzHeatBounds IBMSchwartzSpatialPrimitive
open IBMSchwartzPrimitiveLimit IBMSchwartzSecondProjection GaussianNumberSectors

def endpoint (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T R : ℝ) : GaussianL2 :=
  potential T R • spatialSlope g a n R-weightSlope T R • spatialPrimitive g a n R

theorem weighted_curvature_eq (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ} (hT : 0 < T) (R : ℝ) :
    (∫ r in 0..R, potential T r • projection 2 (mollifiedClass g a n r)) =
      endpoint g a n T R-potential T 0 • spatialSlope g a n 0-
        (2 : ℝ) • spatialPrimitive g a n 0 +
        (4 : ℝ) • ∫ r in 0..R, heatKernel T r • spatialPrimitive g a n r := by
  have hd : ∀ r, HasDerivAt (potential T) (weightSlope T r) r :=
    fun r => potential_spatial_hasDerivAt hT r
  have hdd : ∀ r, HasDerivAt (weightSlope T) (4*heatKernel T r) r :=
    fun r => slope_spatial_hasDerivAt hT r
  have h1 := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (potential_continuous hT).continuousOn (slope_continuous g a n).continuousOn
    (fun r _ => hd r) (fun r _ => spatialSlope_hasDerivAt g a n r)
    ((weightSlope_continuous T).intervalIntegrable 0 R)
    ((projected_continuous g a n).intervalIntegrable 0 R)
  have h2 := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (weightSlope_continuous T).continuousOn (spatialPrimitive_continuous g a n).continuousOn
    (fun r _ => hdd r) (fun r _ => spatialPrimitive_hasDerivAt g a n r)
    (((heatKernel_spatial_continuous T).const_mul 4).intervalIntegrable 0 R)
    ((slope_continuous g a n).intervalIntegrable 0 R)
  rw [h1, h2]
  have hz : weightSlope T 0 = -2 := by norm_num [weightSlope, tail_zero]
  simp only [hz, mul_smul, intervalIntegral.integral_smul]
  unfold endpoint
  module

theorem actual_origin_finite_cancellation (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (T : ℝ≥0) (hT : 0 < T) (R : ℝ) :
    (∫ ω, BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct) •
        spatialSlope g a n 0 +
      (1/2 : ℝ) • (∫ r in 0..R, potential T r • projection 2 (mollifiedClass g a n r)) =
      (2 : ℝ) • (∫ r in 0..R, heatKernel T r • spatialPrimitive g a n r)-
        spatialPrimitive g a n 0+(1/2 : ℝ) • endpoint g a n T R := by
  rw [← IBMClockOriginMean.origin_coefficient_eq_mass_mean,
    weighted_curvature_eq g a n (NNReal.coe_pos.mpr hT) R]
  module

theorem potential_slope_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun R => potential T R • spatialSlope g a n R) atTop (𝓝 0) := by
  obtain ⟨C,hC,hc⟩ := slope_growth g a n
  have ha : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_
    (by simpa only [mul_zero] using
      (shifted_power_density_decay ha 1).const_mul (4*Real.sqrt T*C))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
    (IBMClockHeatOccupation.potential_nonneg hT hR)]
  have he := mul_le_mul (potential_le_density (T := T) hR) (hc R)
    (norm_nonneg _) (mul_nonneg (by positivity) (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _))
  simpa only [pow_one] using he.trans_eq (by ring)

theorem tail_primitive_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun R => weightSlope T R • spatialPrimitive g a n R) atTop (𝓝 0) := by
  have ha : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have ht := (shifted_power_density_decay ha 0).const_mul
    (4*SchwartzMap.seminorm ℝ 0 0 (IBMCorrectionStein.jet g 0))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_
    (by simpa only [pow_zero, mul_one, mul_zero] using ht)
  filter_upwards [eventually_ge_atTop (Real.sqrt T)] with R hR
  have hz : 1 ≤ R/Real.sqrt T := (le_div_iff₀ ha).mpr (by simpa using hR)
  rw [norm_smul, weightSlope, Real.norm_eq_abs, abs_mul, abs_of_nonneg (tail_nonneg _)]
  norm_num
  have hb := primitive_bound g a (IBMGaussianSteinMoments.tripleCoefficient n R 0)
  have he := mul_le_mul
    (mul_le_mul_of_nonneg_left (tail_le_density hz) (by norm_num : (0 : ℝ) ≤ 4))
    hb (norm_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _))
  simpa only [spatialPrimitive] using he.trans_eq (by ring)

theorem endpoint_tendsto_zero (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ} (hT : 0 < T) : Tendsto (endpoint g a n T) atTop (𝓝 0) := by
  change Tendsto (fun R => potential T R • spatialSlope g a n R-
    weightSlope T R • spatialPrimitive g a n R) atTop (𝓝 0)
  simpa only [sub_zero] using
    (potential_slope_tendsto g a n hT).sub (tail_primitive_tendsto g a n hT)

end OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatBoundary
