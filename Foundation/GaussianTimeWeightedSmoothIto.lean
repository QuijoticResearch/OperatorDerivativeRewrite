import Foundation.GaussianContinuousStochasticFubini

/-! A genuine time-dependent smooth Brownian Ito theorem for a(t) f(x),
with a C1 and f in the verified bounded-derivative C3 spatial core. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianTimeWeightedSmoothIto
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianContinuousIntegrands GaussianLipschitzIntegrands GaussianPredictableFull
open GaussianSmoothIto GaussianContinuousStochasticFubini
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

variable {φ : ℝ → ℝ} {K : ℝ≥0}

def primitive (hφ : LipschitzWith K φ) (t : ℝ) : GaussianL2 :=
  ∫ s in 0..t, valueL2 hφ s.toNNReal

theorem primitive_hasDerivAt (hφ : LipschitzWith K φ) (t : ℝ) :
    HasDerivAt (primitive hφ) (valueL2 hφ t.toNNReal) t := by
  have hc := (valueL2_continuous hφ).comp continuous_real_toNNReal
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem primitive_continuous (hφ : LipschitzWith K φ) : Continuous (primitive hφ) :=
  continuous_iff_continuousAt.mpr (fun t => (primitive_hasDerivAt hφ t).continuousAt)

def weightedField (a : ℝ → ℝ) (ha : Continuous a) (hφ : LipschitzWith K φ)
    (T : ℝ≥0) : fullPredictable :=
  predictableField (fun t => a t • valueL2 hφ t)
    ((ha.comp continuous_subtype_val).smul (valueL2_continuous hφ))
    (fun t => ((valueL2_past hφ t).const_smul (a t)).congr
      (Lp.coeFn_smul (a t) (valueL2 hφ t)).symm) T

theorem weightedField_slices (a : ℝ → ℝ) (ha : Continuous a) (hφ : LipschitzWith K φ)
    (T : ℝ≥0) : scalarCurry (weightedField a ha hφ T : TimeProbabilityL2) =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator (fun t => a t • valueL2 hφ t.toNNReal) := by
  have hs := runningField_slices (fun t : ℝ≥0 => a t • valueL2 hφ t)
    ((ha.comp continuous_subtype_val).smul (valueL2_continuous hφ)) T
  filter_upwards [hs] with t ht
  change scalarCurry (weightedField a ha hφ T : TimeProbabilityL2) t = _ at ht
  rw [ht]
  by_cases hm : t ∈ Ioc 0 (T : ℝ)
  · simp only [horizonValue, indicator_of_mem hm, Real.coe_toNNReal _ hm.1.le]
  · simp [horizonValue, hm]

theorem weighted_primitive_identity (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a)
    (hφ : LipschitzWith K φ) (T : ℝ≥0) :
    (∫ t in 0..(T : ℝ), deriv a t • primitive hφ t) +
      (∫ t in 0..(T : ℝ), a t • valueL2 hφ t.toNNReal) = a T • primitive hφ T := by
  have hda := ha.continuous_deriv (by norm_num)
  have hd (t : ℝ) : HasDerivAt (fun t => a t • primitive hφ t)
      (deriv a t • primitive hφ t + a t • valueL2 hφ t.toNNReal) t :=
    by
      convert ((ha.differentiable (by norm_num) t).hasDerivAt).smul
        (primitive_hasDerivAt hφ t) using 1 <;> (try funext x) <;>
        (try simp only [Pi.smul_apply]) <;> module
  have hi1 : IntervalIntegrable (fun t : ℝ => deriv a t • primitive hφ t) volume 0 T :=
    (hda.smul (primitive_continuous hφ)).intervalIntegrable 0 (T : ℝ)
  have hi2 : IntervalIntegrable (fun t : ℝ => a t • valueL2 hφ t.toNNReal) volume 0 T :=
    (ha.continuous.smul ((valueL2_continuous hφ).comp continuous_real_toNNReal)).intervalIntegrable 0 (T : ℝ)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at he
  simpa only [primitive, intervalIntegral.integral_same, smul_zero, sub_zero] using he

variable (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) {K0 K1 K2 : ℝ≥0}
  (h0 : LipschitzWith K0 f) (h1 : LipschitzWith K1 (deriv f))
  (h2 : LipschitzWith K2 (deriv (deriv f)))
  (M : ℝ) (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M)

include hf h0 h2 M hM in
theorem smooth_integrand_continuous : Continuous (integrand h1) := by
  apply itoIntegral.isometry.comp_continuous_iff.mp
  have he : (fun t => itoIntegral (integrand h1 t)) =
      fun t => valueL2 h0 t - valueL2 h0 0 - (1 / 2 : ℝ) • primitive h2 t := by
    funext t
    have h := ito_of_lipschitz_derivatives f hf h0 h1 h2 M hM t
    change _ = _ + (1 / 2 : ℝ) • primitive h2 t at h
    linear_combination (norm := module) -h
  change Continuous (fun t => itoIntegral (integrand h1 t))
  rw [he]
  exact ((valueL2_continuous h0).sub continuous_const).sub
    (continuous_smul.comp (continuous_const.prodMk
      ((primitive_continuous h2).comp continuous_subtype_val)))

include hf h0 h2 M hM in
theorem weightedField_eq (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a) (T : ℝ≥0) :
    weightedField a ha.continuous h1 T =
      a T • integrand h1 T - ∫ t in 0..(T : ℝ), deriv a t • integrand h1 t.toNNReal := by
  apply Subtype.ext
  apply scalarCurry.injective
  apply Lp.ext
  exact (weightedField_slices a ha.continuous h1 T).trans
    (weighted_slices (valueL2 h1) (valueL2_continuous h1) (integrand h1)
      (smooth_integrand_continuous f hf h0 h1 h2 M hM) (integrand_slices h1)
      a (deriv a) ha.continuous (ha.continuous_deriv (by norm_num))
      (fun t => (ha.differentiable (by norm_num) t).hasDerivAt) T).symm

include hf M hM in
/-- Time-dependent Ito for a(t) f(x), with independently constructed running
integrand a(t) f'(B_t). The deterministic coefficient only needs C1 regularity. -/
theorem time_weighted_ito (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a) (T : ℝ≥0) :
    a T • valueL2 h0 T - a 0 • valueL2 h0 0 =
      itoIntegral (weightedField a ha.continuous h1 T) +
        (∫ t in 0..(T : ℝ), deriv a t • valueL2 h0 t.toNNReal) +
        (1 / 2 : ℝ) • (∫ t in 0..(T : ℝ), a t • valueL2 h2 t.toNNReal) := by
  have hda := ha.continuous_deriv (by norm_num)
  have hU := smooth_integrand_continuous f hf h0 h1 h2 M hM
  have hJ (t : ℝ≥0) : itoIntegral (integrand h1 t) =
      valueL2 h0 t - valueL2 h0 0 - (1 / 2 : ℝ) • primitive h2 t := by
    have h := ito_of_lipschitz_derivatives f hf h0 h1 h2 M hM t
    change _ = _ + (1 / 2 : ℝ) • primitive h2 t at h
    linear_combination (norm := module) -h
  have hiF : IntervalIntegrable (fun t : ℝ => deriv a t • valueL2 h0 t.toNNReal) volume 0 T :=
    (hda.smul ((valueL2_continuous h0).comp continuous_real_toNNReal)).intervalIntegrable _ _
  have hi0 : IntervalIntegrable (fun t : ℝ => deriv a t • valueL2 h0 0) volume 0 T :=
    (hda.smul continuous_const).intervalIntegrable _ _
  have hiV : IntervalIntegrable (fun t : ℝ => deriv a t • primitive h2 t) volume 0 T :=
    (hda.smul (primitive_continuous h2)).intervalIntegrable _ _
  have hiV2 : IntervalIntegrable (fun t : ℝ => (1 / 2 : ℝ) • (deriv a t • primitive h2 t)) volume 0 T :=
    hiV.smul (1 / 2 : ℝ)
  have htime : (∫ t in 0..(T : ℝ), deriv a t) = a T - a 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (ha.differentiable (by norm_num) t).hasDerivAt) (hda.intervalIntegrable _ _)
  have hint : (∫ t in 0..(T : ℝ), deriv a t • itoIntegral (integrand h1 t.toNNReal)) =
      (∫ t in 0..(T : ℝ), deriv a t • valueL2 h0 t.toNNReal) -
        (a T - a 0) • valueL2 h0 0 -
        (1 / 2 : ℝ) • (∫ t in 0..(T : ℝ), deriv a t • primitive h2 t) := by
    calc
      _ = ∫ t in 0..(T : ℝ), (deriv a t • valueL2 h0 t.toNNReal -
          deriv a t • valueL2 h0 0) - (1 / 2 : ℝ) • (deriv a t • primitive h2 t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [hJ]
        rw [Real.coe_toNNReal _ ((uIcc_of_le T.coe_nonneg ▸ ht).1)]
        module
      _ = _ := by
        rw [intervalIntegral.integral_sub (hiF.sub hi0) hiV2,
          intervalIntegral.integral_sub hiF hi0, intervalIntegral.integral_smul,
          intervalIntegral.integral_smul_const, htime]
  have hi := integral_weighted_field (integrand h1) hU a (deriv a) hda T
  rw [← weightedField_eq f hf h0 h1 h2 M hM a ha T, hJ, hint] at hi
  have hp := weighted_primitive_identity a ha h2 T
  linear_combination (norm := module) -hi - (1 / 2 : ℝ) • hp

include hf M hM in
/-- The same formula with the actual time/space generator combined in one
integrable Bochner drift. Both partial derivatives are independently verified below. -/
theorem time_weighted_ito_combined (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a) (T : ℝ≥0) :
    a T • valueL2 h0 T - a 0 • valueL2 h0 0 =
      itoIntegral (weightedField a ha.continuous h1 T) +
        ∫ t in 0..(T : ℝ), deriv a t • valueL2 h0 t.toNNReal +
          (1 / 2 : ℝ) • (a t • valueL2 h2 t.toNNReal) := by
  have hi1 : IntervalIntegrable (fun t : ℝ => deriv a t • valueL2 h0 t.toNNReal) volume 0 T :=
    ((ha.continuous_deriv (by norm_num)).smul
      ((valueL2_continuous h0).comp continuous_real_toNNReal)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => a t • valueL2 h2 t.toNNReal) volume 0 T :=
    (ha.continuous.smul ((valueL2_continuous h2).comp continuous_real_toNNReal)).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun t : ℝ => (1 / 2 : ℝ) • (a t • valueL2 h2 t.toNNReal)) volume 0 T :=
    hi2.smul (1 / 2 : ℝ)
  rw [intervalIntegral.integral_add hi1 hi3, intervalIntegral.integral_smul, ← add_assoc]
  exact time_weighted_ito f hf h0 h1 h2 M hM a ha T

theorem time_partial (a g : ℝ → ℝ) (ha : Differentiable ℝ a) (t x : ℝ) :
    HasDerivAt (fun s => a s * g x) (deriv a t * g x) t := (ha t).hasDerivAt.mul_const _

theorem space_partial (a g : ℝ → ℝ) (hg : Differentiable ℝ g) (t x : ℝ) :
    HasDerivAt (fun y => a t * g y) (a t * deriv g x) x := (hg x).hasDerivAt.const_mul _

theorem second_space_partial (a g : ℝ → ℝ) (hg : Differentiable ℝ g)
    (hg' : Differentiable ℝ (deriv g)) (t x : ℝ) :
    HasDerivAt (deriv (fun y => a t * g y)) (a t * deriv (deriv g) x) x := by
  have he : deriv (fun y => a t * g y) = fun y => a t * deriv g y :=
    funext fun y => (space_partial a g hg t y).deriv
  rw [he]
  exact (hg' x).hasDerivAt.const_mul _

end OperatorDerivativeRewrite.Foundation.GaussianTimeWeightedSmoothIto



