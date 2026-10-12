import Foundation.GaussianSmoothIto
import Foundation.GaussianHermiteMartingale

/-! Conditional smooth Brownian Ito and Dynkin identities for the actual
raw-past conditional projection. The drift is a genuine Bochner L2 integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianSmoothConditional
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianContinuousIntegrands GaussianLipschitzIntegrands GaussianPredictableFull
open GaussianPredictableCutoff GaussianConditionalIto GaussianConditionalClarkOcone
open GaussianHermiteMartingale GaussianSmoothIto

theorem cut_predictableField (v : ℝ≥0 → GaussianL2) (hv : Continuous v)
    (ha : ∀ t, AEStronglyMeasurable[naturalFiltration t] (v t) gaussianProduct) (S T : ℝ≥0) :
    predictableCut S (predictableField v hv ha T) = predictableField v hv ha (min S T) := by
  apply Subtype.ext
  apply scalarCurry.injective
  apply Lp.ext
  filter_upwards [scalarCurry_cut S (predictableField v hv ha T), runningField_slices v hv T,
    runningField_slices v hv (min S T)] with t hc ht hm
  change scalarCurry (cut S (runningField v hv T)) t =
    scalarCurry (runningField v hv (min S T)) t
  change scalarCurry (cut S (runningField v hv T)) t =
    (Ioc 0 (S : ℝ)).indicator (scalarCurry (runningField v hv T)) t at hc
  rw [hc, hm]
  by_cases hs : t ∈ Ioc 0 (S : ℝ)
  · rw [indicator_of_mem hs, ht]
    have he : t ∈ Ioc 0 (min (S : ℝ) (T : ℝ)) ↔ t ∈ Ioc 0 (T : ℝ) := by
      simp only [mem_Ioc, le_min_iff]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hs.2, h.2⟩⟩
    by_cases hT : t ∈ Ioc 0 (T : ℝ) <;>
      simp [GaussianContinuousIntegrands.horizonValue, NNReal.coe_min, hT, he]
  · have he : t ∉ Ioc 0 (min (S : ℝ) (T : ℝ)) :=
      fun hh => hs ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    simp [hs, GaussianContinuousIntegrands.horizonValue, NNReal.coe_min, he]

theorem cut_integrand {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (S T : ℝ≥0) :
    predictableCut S (integrand hφ T) = integrand hφ (min S T) :=
  cut_predictableField _ _ _ S T

theorem pastProjection_drift {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (T : ℝ≥0) :
    pastProjection T (∫ t in 0..(T : ℝ), valueL2 hφ t.toNNReal) =
      ∫ t in 0..(T : ℝ), valueL2 hφ t.toNNReal := by
  rw [← (pastProjection T).intervalIntegral_comp_comm (drift_integrable hφ T)]
  apply intervalIntegral.integral_congr
  intro t ht
  change pastProjection T (valueL2 hφ t.toNNReal) = valueL2 hφ t.toNNReal
  apply Submodule.starProjection_eq_self_iff.mpr
  have htT : t.toNNReal ≤ T :=
    Real.toNNReal_le_iff_le_coe.mpr ((uIcc_of_le T.coe_nonneg ▸ ht).2)
  exact (valueL2_past hφ t.toNNReal).mono (naturalFiltration.mono htT)

variable (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) {K0 K1 K2 : ℝ≥0}
  (h0 : LipschitzWith K0 f) (h1 : LipschitzWith K1 (deriv f))
  (h2 : LipschitzWith K2 (deriv (deriv f)))
  (M : ℝ) (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M)

include hf h1 M hM

/-- Genuine conditional martingale identity for the second-derivative compensated
smooth process, not a prescribed martingale correction. -/
theorem pastProjection_compensated (S T : ℝ≥0) :
    pastProjection S (valueL2 h0 T - (1 / 2 : ℝ) •
      (∫ t in 0..(T : ℝ), valueL2 h2 t.toNNReal)) =
    valueL2 h0 (min S T) - (1 / 2 : ℝ) •
      (∫ t in 0..(min S T : ℝ≥0), valueL2 h2 t.toNNReal) := by
  have he (R : ℝ≥0) : valueL2 h0 R - (1 / 2 : ℝ) •
      (∫ t in 0..(R : ℝ), valueL2 h2 t.toNNReal) =
      valueL2 h0 0 + itoIntegral (integrand h1 R) := by
    have h := ito_of_lipschitz_derivatives f hf h0 h1 h2 M hM R
    linear_combination (norm := module) h
  rw [he T, he (min S T), map_add, pastProjection_integral, cut_integrand,
    GaussianSmoothIto.valueL2_zero, map_smul, pastProjection_one]

/-- Conditional Dynkin with actual generator (1/2) f'' and no hidden
terminal-projection/running-derivative substitution. -/
theorem smooth_conditional_dynkin (S T : ℝ≥0) (hST : S ≤ T) :
    pastProjection S (valueL2 h0 T) - valueL2 h0 S =
      (1 / 2 : ℝ) • pastProjection S
        (∫ t in (S : ℝ)..(T : ℝ), valueL2 h2 t.toNNReal) := by
  have h := pastProjection_compensated f hf h0 h1 h2 M hM S T
  rw [min_eq_left hST, map_sub, map_smul] at h
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (drift_integrable h2 S)
    (((valueL2_continuous h2).comp continuous_real_toNNReal).intervalIntegrable (S : ℝ) (T : ℝ))
  rw [← hadd, map_add, pastProjection_drift] at h
  linear_combination (norm := module) h

end OperatorDerivativeRewrite.Foundation.GaussianSmoothConditional

