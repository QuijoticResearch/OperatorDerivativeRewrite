import Foundation.IBMHeatTailDecay
import Foundation.IBMSceneryGlobalGrowth

/-! Remove the finite-radius boundary term using bounds on the actual
source fields. Constants may depend on the fixed mollifier. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticHeatEndpoint
open InfiniteGaussian IBMClockGaussianTail IBMClockHeatPotential IBMClockHeatOccupation
open IBMHeatTailDecay IBMQuarticHeatBoundary IBMQuarticSecondPrimitive
open IBMQuarticPrimitiveLimit IBMQuarticSecondChaos IBMQuadraticSpatialCalculus
open IBMGaussianSteinMoments GaussianTimeSpaceHermite

theorem cross_growth (n : ℕ) (i j : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖cross (tripleCoefficient n r i) (tripleCoefficient n r j)‖ ≤
      C*(1+|r|)^2 := by
  obtain ⟨A,hA,ha⟩ := IBMSceneryGlobalGrowth.tripleCoefficient_global_growth n i
  obtain ⟨B,hB,hb⟩ := IBMSceneryGlobalGrowth.tripleCoefficient_global_growth n j
  refine ⟨2*A*B, by positivity, fun r => ?_⟩
  have he := mul_le_mul (mul_le_mul_of_nonneg_left (ha r) (by norm_num : (0 : ℝ) ≤ 2))
    (hb r) (norm_nonneg (tripleCoefficient n r j)) (by positivity : 0 ≤ 2*(A*(1+|r|)))
  have hc := cross_norm_le (tripleCoefficient n r i) (tripleCoefficient n r j)
  nlinarith

theorem slope_growth (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖slope n r‖ ≤ C*(1+|r|)^3 := by
  obtain ⟨A,hA,ha⟩ := cross_growth n 0 0
  obtain ⟨B,hB,hb⟩ := cross_growth n 0 1
  refine ⟨A+4*B, by positivity, fun r => ?_⟩
  have hw : ‖(wick (tripleCoefficient n r 0) 2 : GaussianL2)‖ ≤ A*(1+|r|)^2 := by
    rw [← cross_self]; exact ha r
  have hc : ‖IBMVarianceClockGeometry.variance n r‖ ≤ 2*(1+|r|) :=
    (IBMVarianceClockGeometry.variance_bound n r).trans (by linarith [abs_nonneg r])
  have h₁ := mul_le_mul (IBMVarianceClockGeometry.slope_bound n r) hw
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h₂ := mul_le_mul hc (mul_le_mul_of_nonneg_left (hb r) (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity : 0 ≤ 2*‖cross (tripleCoefficient n r 0) (tripleCoefficient n r 1)‖)
    (by positivity : 0 ≤ 2*(1+|r|))
  have hq : (1+|r|)^2 ≤ (1+|r|)^3 :=
    pow_le_pow_right₀ (by linarith [abs_nonneg r]) (by norm_num)
  have he : ‖slope n r‖ ≤ ‖deriv (IBMVarianceClockGeometry.variance n) r‖ *
      ‖(wick (tripleCoefficient n r 0) 2 : GaussianL2)‖ +
      ‖IBMVarianceClockGeometry.variance n r‖ *
        (2*‖cross (tripleCoefficient n r 0) (tripleCoefficient n r 1)‖) := by
    rw [IBMQuarticSecondPrimitive.slope, norm_smul]
    norm_num
    have hh := norm_add_le
      (deriv (IBMVarianceClockGeometry.variance n) r • (wick (tripleCoefficient n r 0) 2 : GaussianL2))
      (IBMVarianceClockGeometry.variance n r •
        ((2 : ℝ) • cross (tripleCoefficient n r 0) (tripleCoefficient n r 1)))
    simp only [norm_smul] at hh
    norm_num at hh
    nlinarith [norm_nonneg (deriv (IBMVarianceClockGeometry.variance n) r •
      (wick (tripleCoefficient n r 0) 2 : GaussianL2) +
      IBMVarianceClockGeometry.variance n r •
        ((2 : ℝ) • cross (tripleCoefficient n r 0) (tripleCoefficient n r 1)))]
  have hAq := mul_le_mul_of_nonneg_left hq hA
  nlinarith

theorem potential_slope_tendsto (n : ℕ) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun R => potential T R • slope n R) atTop (𝓝 0) := by
  obtain ⟨C,hC,hc⟩ := slope_growth n
  have ha : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_
    (by simpa only [mul_zero] using (shifted_power_density_decay ha 3).const_mul (4*Real.sqrt T*C))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (potential_nonneg hT hR)]
  have he := mul_le_mul (potential_le_density (T := T) hR) (hc R)
    (norm_nonneg _) (mul_nonneg (by positivity) (gaussianPDFReal_nonneg _ _ _))
  nlinarith

theorem tail_primitive_tendsto (n : ℕ) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun R => weightSlope T R • primitive n R) atTop (𝓝 0) := by
  have ha : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_
    (by simpa only [mul_zero] using (shifted_power_density_decay ha 2).const_mul (16 : ℝ))
  filter_upwards [eventually_ge_atTop (Real.sqrt T)] with R hR
  have hR0 : 0 ≤ R := ha.le.trans hR
  have hz : 1 ≤ R/Real.sqrt T := (le_div_iff₀ ha).mpr (by simpa using hR)
  rw [norm_smul, weightSlope, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (tail_nonneg _)]
  norm_num
  have hb : ‖primitive n R‖ ≤ 4*(1+|R|)^2 := by
    have he := primitive_bound n R
    nlinarith [abs_nonneg R]
  have he := mul_le_mul (mul_le_mul_of_nonneg_left (tail_le_density hz) (by norm_num : (0 : ℝ) ≤ 4))
    hb (norm_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (gaussianPDFReal_nonneg _ _ _))
  nlinarith

/-- The actual source-L2 endpoint in the finite-radius identity vanishes. -/
theorem endpoint_tendsto_zero (n : ℕ) {T : ℝ} (hT : 0 < T) :
    Tendsto (endpoint n T) atTop (𝓝 0) := by
  change Tendsto (fun R => potential T R • slope n R - weightSlope T R • primitive n R) atTop (𝓝 0)
  simpa only [sub_zero] using
    (potential_slope_tendsto n hT).sub (tail_primitive_tendsto n hT)

end OperatorDerivativeRewrite.Foundation.IBMQuarticHeatEndpoint
