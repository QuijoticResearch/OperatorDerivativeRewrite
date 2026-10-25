import Foundation.IBMMixedClockLimit

/-! Bounded clock weights preserve the actual mixed-cap L1 limit.
Weights may depend on all observations; no conditional projection is used. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMBoundedMixedClockTesting
open InfiniteGaussian IBMMixedClockSelection IBMMixedClockLimit
open IBMRawGridMixedObservable

variable (w : SampleSpace → ℝ) (hw : Measurable w) {C : ℝ} (hC : ∀ Y, ‖w Y‖ ≤ C)
include hw hC

theorem weighted_integrable {f : SampleSpace → ℝ} (hf : Integrable f gaussianProduct) :
    Integrable (fun Y => w Y*f Y) gaussianProduct :=
  hf.bdd_mul hw.aestronglyMeasurable (ae_of_all _ hC)

theorem weighted_error_bound (H R S : ℝ≥0) (N : ℕ) :
    |(∫ Y, w Y*mixedSum H R S N Y ∂gaussianProduct)-
      (∫ Y, w Y*mixedOccupation H R S Y ∂gaussianProduct)| ≤
        C*(∫ Y, |mixedSum H R S N Y-mixedOccupation H R S Y| ∂gaussianProduct) := by
  have hf := weighted_integrable w hw hC (mixedSum_integrable H R S N)
  have hg := weighted_integrable w hw hC (mixedOccupation_integrable H R S)
  rw [← integral_sub hf hg,← integral_const_mul]
  calc
    _ ≤ ∫ Y, ‖w Y*mixedSum H R S N Y-w Y*mixedOccupation H R S Y‖ ∂gaussianProduct := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun Y => w Y*mixedSum H R S N Y-w Y*mixedOccupation H R S Y)
    _ ≤ _ := integral_mono (hf.sub hg).norm
      (((mixedSum_integrable H R S N).sub (mixedOccupation_integrable H R S)).abs.const_mul C)
      fun Y => by
        rw [← mul_sub,norm_mul,Real.norm_eq_abs (mixedSum H R S N Y-mixedOccupation H R S Y)]
        exact mul_le_mul_of_nonneg_right (hC Y) (abs_nonneg _)

theorem weighted_mean_tendsto (H R S : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => ∫ Y, w Y*mixedSum H R S N Y ∂gaussianProduct) atTop
      (𝓝 (∫ Y, w Y*mixedOccupation H R S Y ∂gaussianProduct)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := (mixed_actual_absolute_tendsto H R S hH).const_mul C
  simp only [mul_zero] at h
  exact squeeze_zero (fun N => norm_nonneg _) (fun N => by
    simpa only [Real.norm_eq_abs] using weighted_error_bound w hw hC H R S N) h

theorem weighted_energy_tendsto (H R S : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N : ℕ => ∫ Y, w Y*mixedEnergy (H/(N+1)) (N+1) R S Y ∂gaussianProduct) atTop
      (𝓝 (∫ Y, w Y*(IBMClippedClockCrossing.cap (GaussianTimeProcess.process R Y) (GaussianTimeProcess.process H Y)*
        IBMClippedClockCrossing.cap (GaussianTimeProcess.process S Y) (GaussianTimeProcess.process H Y)-
          mixedOccupation H R S Y) ∂gaussianProduct)) := by
  have he := weighted_integrable w hw hC (mixed_endpoint_integrable H R S)
  have ho := weighted_integrable w hw hC (mixedOccupation_integrable H R S)
  have h := (tendsto_const_nhds (x:=∫ Y, w Y*(IBMClippedClockCrossing.cap (GaussianTimeProcess.process R Y)
    (GaussianTimeProcess.process H Y)*IBMClippedClockCrossing.cap (GaussianTimeProcess.process S Y)
      (GaussianTimeProcess.process H Y)) ∂gaussianProduct)).sub (weighted_mean_tendsto w hw hC H R S hH)
  have hi := integral_sub he ho
  simp_rw [← mul_sub] at hi
  rw [← hi] at h
  apply h.congr'
  exact Eventually.of_forall fun N => by
    simp_rw [mixedEnergy_identity,mul_sub]
    exact (integral_sub he (weighted_integrable w hw hC (mixedSum_integrable H R S N))).symm

end OperatorDerivativeRewrite.Foundation.IBMBoundedMixedClockTesting
