import Foundation.GaussianShiftedHermite

/-! Actual shifted Hermite representation from quantitatively convergent stochastic sums. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianShiftedRepresentation
open InfiniteGaussian GaussianShiftedHermite GaussianBrownianQuadraticVariation
open GaussianPredictableFull GaussianPredictableAdjoint
open GaussianHermiteRepresentation (uniform_power_error_upper)

theorem uniform_stochasticSum_error_bound (s : ℝ≥0) (n N : ℕ) (T : ℝ≥0) :
    ‖(incrementCore s T (n + 1) : GaussianL2) -
      (n + 1 : ℝ) • itoIntegral (stepSum s n (uniformTime T N))‖ ^ 2 ≤
        ((n + 1).factorial : ℝ) * (n + 1 : ℝ) * (T : ℝ) ^ (n + 1) / (N + 1) := by
  have he := stochasticSum_error s n (uniformTime T N) (uniformTime_monotone T N)
  rw [(uniformTime_endpoints T N).2] at he
  rw [he]
  calc
    _ ≤ ((n + 1).factorial : ℝ) * ((n + 1 : ℝ) * ((T : ℝ) / (N + 1)) * (T : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left (uniform_power_error_upper n N T) (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem scaled_stochasticSum_tendsto (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) :
    Tendsto (fun N => (n + 1 : ℝ) • itoIntegral (stepSum s n (uniformTime T N))) atTop
      (𝓝 (incrementCore s T (n + 1) : GaussianL2)) := by
  have ht : Tendsto (fun N : ℕ => ((n + 1).factorial : ℝ) * (n + 1 : ℝ) *
      (T : ℝ) ^ (n + 1) / (N + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hs := squeeze_zero (fun N => sq_nonneg _)
    (fun N => uniform_stochasticSum_error_bound s n N T) ht
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using hh

theorem stochasticSum_tendsto (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) :
    Tendsto (fun N => itoIntegral (stepSum s n (uniformTime T N))) atTop
      (𝓝 ((n + 1 : ℝ)⁻¹ • (incrementCore s T (n + 1) : GaussianL2))) := by
  have h := (scaled_stochasticSum_tendsto s n T).const_smul (n + 1 : ℝ)⁻¹
  simpa only [smul_smul, inv_mul_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), one_smul] using h

theorem hermite_mem_integralRange (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) :
    (n + 1 : ℝ)⁻¹ • (incrementCore s T (n + 1) : GaussianL2) ∈ itoIntegral.toLinearMap.range :=
  GaussianBrownianGeneratedSpace.integralRange_isClosed.mem_of_tendsto
    (stochasticSum_tendsto s n T) (Eventually.of_forall fun N => ⟨stepSum s n (uniformTime T N), rfl⟩)

def hermiteIntegrand (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) : fullPredictable :=
  predictableAdjoint ((n + 1 : ℝ)⁻¹ • (incrementCore s T (n + 1) : GaussianL2))

theorem integral_hermiteIntegrand (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) :
    itoIntegral (hermiteIntegrand s n T) = (n + 1 : ℝ)⁻¹ • (incrementCore s T (n + 1) : GaussianL2) := by
  obtain ⟨u, hu⟩ := hermite_mem_integralRange s n T
  change itoIntegral u = _ at hu
  unfold hermiteIntegrand
  rw [← hu, predictableAdjoint_integral]

theorem hermite_representation (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) :
    (incrementCore s T (n + 1) : GaussianL2) = (n + 1 : ℝ) • itoIntegral (hermiteIntegrand s n T) := by
  rw [integral_hermiteIntegrand, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

theorem stepSum_tendsto (s : ℝ≥0) (n : ℕ) (T : ℝ≥0) :
    Tendsto (fun N => stepSum s n (uniformTime T N)) atTop (𝓝 (hermiteIntegrand s n T)) := by
  have h := predictableAdjoint.continuous.continuousAt.tendsto.comp (stochasticSum_tendsto s n T)
  simpa only [Function.comp_def, predictableAdjoint_integral, hermiteIntegrand] using h


end OperatorDerivativeRewrite.Foundation.GaussianShiftedRepresentation
