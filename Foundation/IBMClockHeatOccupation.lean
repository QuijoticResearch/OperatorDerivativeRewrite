import Foundation.IBMClockHeatPotential
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! Identify the explicit half-line potential with an actual time integral
of the Gaussian density, including its singular initial-time endpoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockHeatOccupation
open IBMClockGaussianTail IBMClockHeatPotential

theorem density_le_origin (r : ℝ) : density r ≤ density 0 := by
  simp only [density, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  exact mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) (by norm_num)))

theorem heatKernel_nonneg (t r : ℝ) : 0 ≤ heatKernel t r := by
  exact div_nonneg (gaussianPDFReal_nonneg _ _ _) (Real.sqrt_nonneg _)

theorem heatKernel_time_measurable (r : ℝ) : Measurable (fun t => heatKernel t r) :=
  (density_continuous.measurable.comp (measurable_const.div Real.continuous_sqrt.measurable)).div
    Real.continuous_sqrt.measurable

theorem heatKernel_bound {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    heatKernel t r ≤ density 0 * t ^ (-(1/2 : ℝ)) := by
  rw [Real.rpow_neg ht, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (density_le_origin _) (Real.sqrt_nonneg _)

theorem heatKernel_time_integrable (r : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => heatKernel t r) volume 0 T := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
    (by norm_num : -1 < -(1/2 : ℝ))).const_mul (density 0)
  apply hi.mono_fun' (heatKernel_time_measurable r).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [uIoc_of_le hT] at ht
  rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg t r)]
  exact heatKernel_bound ht.1.le r

theorem sqrt_density_tendsto_zero (r : ℝ) :
    Tendsto (fun t => Real.sqrt t*density (r/Real.sqrt t)) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero (fun t => mul_nonneg (Real.sqrt_nonneg _) (gaussianPDFReal_nonneg _ _ _))
    (fun t => mul_le_mul_of_nonneg_left (density_le_origin _) (Real.sqrt_nonneg _))
  simpa using ((Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds).mul_const (density 0)

theorem scaled_tail_tendsto_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun t => tail (r/Real.sqrt t)) (𝓝[>] 0) (𝓝 0) := by
  have hs : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Real.sqrt_pos.mpr ht
  have hd : Tendsto (fun t => r/Real.sqrt t) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using hs.inv_tendsto_nhdsGT_zero.const_mul_atTop hr
  exact tail_tendsto_zero.comp hd

theorem potential_initial_limit {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun t => potential t r) (𝓝[>] 0) (𝓝 0) := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    have hs : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [potential_zero, mul_assoc, mul_zero, zero_mul] using
      (hs.const_mul 4).mul_const (density 0)
  · simpa only [potential, mul_zero, sub_zero] using
      ((sqrt_density_tendsto_zero r).sub ((scaled_tail_tendsto_zero hr).const_mul r)).const_mul 4

/-- Genuine time integral identity, with no occupation-mean assumption. -/
theorem potential_eq_time_integral {T r : ℝ} (hT : 0 < T) (hr : 0 ≤ r) :
    potential T r = 2 * ∫ s in 0..T, heatKernel s r := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hT
    (fun s hs => potential_time_hasDerivAt hs.1 r)
    ((heatKernel_time_integrable r hT.le).const_mul 2)
    (potential_initial_limit hr)
    ((potential_time_hasDerivAt hT r).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [intervalIntegral.integral_const_mul, sub_zero] using he.symm

theorem potential_nonneg {T r : ℝ} (hT : 0 < T) (hr : 0 ≤ r) : 0 ≤ potential T r := by
  rw [potential_eq_time_integral hT hr]
  exact mul_nonneg (by norm_num)
    (intervalIntegral.integral_nonneg_of_forall hT.le (fun s => heatKernel_nonneg s r))

end OperatorDerivativeRewrite.Foundation.IBMClockHeatOccupation
