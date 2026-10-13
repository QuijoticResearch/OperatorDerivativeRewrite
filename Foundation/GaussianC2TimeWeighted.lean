import Foundation.GaussianC2Ito
import Foundation.GaussianBoundedContinuity
import Foundation.GaussianTimeWeightedSmoothIto

/-! Actual C1 time weights for the genuine bounded-derivative C2 spatial core.
This is the finite-rank time-space route, not arbitrary C1,2 approximation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianC2TimeWeighted
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianContinuousIntegrands GaussianLipschitzIntegrands GaussianPredictableFull
open GaussianC2Ito GaussianContinuousStochasticFubini GaussianTimeWeightedSmoothIto
open GaussianBoundedContinuity
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe
variable (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K0 K1 : ℝ≥0)
  (h0 : ∀ x, ‖deriv f x‖₊ ≤ K0) (h1 : ∀ x, ‖deriv (deriv f) x‖₊ ≤ K1)

theorem curvature_continuous : Continuous (curvatureValue f hf K1 h1) :=
  boundedValue_continuous (second_continuous f hf)
    (fun x => show ‖deriv (deriv f) x‖ ≤ (K1:ℝ) from h1 x)

def primitive (t : ℝ) : GaussianL2 := ∫ s in 0..t, curvatureValue f hf K1 h1 s.toNNReal

theorem primitive_hasDerivAt (t : ℝ) :
    HasDerivAt (primitive f hf K1 h1) (curvatureValue f hf K1 h1 t.toNNReal) t := by
  have hc := (curvature_continuous f hf K1 h1).comp continuous_real_toNNReal
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem primitive_continuous : Continuous (primitive f hf K1 h1) :=
  continuous_iff_continuousAt.mpr (fun t => (primitive_hasDerivAt f hf K1 h1 t).continuousAt)

theorem weighted_primitive_identity (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a)
    (T : ℝ≥0) :
    (∫ t in 0..(T : ℝ), deriv a t • primitive f hf K1 h1 t) +
      (∫ t in 0..(T : ℝ), a t • curvatureValue f hf K1 h1 t.toNNReal) = a T • primitive f hf K1 h1 T := by
  have hda := ha.continuous_deriv (by norm_num)
  have hd (t : ℝ) : HasDerivAt (fun t => a t • primitive f hf K1 h1 t)
      (deriv a t • primitive f hf K1 h1 t + a t • curvatureValue f hf K1 h1 t.toNNReal) t :=
    by
      convert ((ha.differentiable (by norm_num) t).hasDerivAt).smul
        (primitive_hasDerivAt f hf K1 h1 t) using 1 <;> (try funext x) <;>
        (try simp only [Pi.smul_apply]) <;> module
  have hi1 : IntervalIntegrable (fun t : ℝ => deriv a t • primitive f hf K1 h1 t) volume 0 T :=
    (hda.smul (primitive_continuous f hf K1 h1)).intervalIntegrable 0 (T : ℝ)
  have hi2 : IntervalIntegrable (fun t : ℝ => a t • curvatureValue f hf K1 h1 t.toNNReal) volume 0 T :=
    (ha.continuous.smul ((curvature_continuous f hf K1 h1).comp continuous_real_toNNReal)).intervalIntegrable 0 (T : ℝ)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at he
  simpa only [primitive, intervalIntegral.integral_same, smul_zero, sub_zero] using he


include K0 h0 in
theorem smooth_integrand_continuous : Continuous (integrand (derivativeLip f hf K1 h1)) := by
  apply itoIntegral.isometry.comp_continuous_iff.mp
  have he : (fun t => itoIntegral (integrand (derivativeLip f hf K1 h1) t)) =
      fun t => valueL2 (functionLip f hf K0 h0) t - valueL2 (functionLip f hf K0 h0) 0 - (1 / 2 : ℝ) • primitive f hf K1 h1 t := by
    funext t
    have h := c2_ito f hf K0 K1 h0 h1 t
    change _ = _ + (1 / 2 : ℝ) • primitive f hf K1 h1 t at h
    linear_combination (norm := module) -h
  change Continuous (fun t => itoIntegral (integrand (derivativeLip f hf K1 h1) t))
  rw [he]
  exact ((valueL2_continuous (functionLip f hf K0 h0)).sub continuous_const).sub
    (continuous_smul.comp (continuous_const.prodMk
      ((primitive_continuous f hf K1 h1).comp continuous_subtype_val)))

include K0 h0 in
theorem weightedField_eq (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a) (T : ℝ≥0) :
    weightedField a ha.continuous (derivativeLip f hf K1 h1) T =
      a T • integrand (derivativeLip f hf K1 h1) T - ∫ t in 0..(T : ℝ), deriv a t • integrand (derivativeLip f hf K1 h1) t.toNNReal := by
  apply Subtype.ext
  apply scalarCurry.injective
  apply Lp.ext
  exact (weightedField_slices a ha.continuous (derivativeLip f hf K1 h1) T).trans
    (weighted_slices (valueL2 (derivativeLip f hf K1 h1)) (valueL2_continuous (derivativeLip f hf K1 h1)) (integrand (derivativeLip f hf K1 h1))
      (smooth_integrand_continuous f hf K0 K1 h0 h1) (integrand_slices (derivativeLip f hf K1 h1))
      a (deriv a) ha.continuous (ha.continuous_deriv (by norm_num))
      (fun t => (ha.differentiable (by norm_num) t).hasDerivAt) T).symm


/-- Time-dependent Ito for a(t) f(x), with independently constructed running
integrand a(t) f'(B_t). The deterministic coefficient only needs C1 regularity. -/
theorem time_weighted_ito (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a) (T : ℝ≥0) :
    a T • valueL2 (functionLip f hf K0 h0) T - a 0 • valueL2 (functionLip f hf K0 h0) 0 =
      itoIntegral (weightedField a ha.continuous (derivativeLip f hf K1 h1) T) +
        (∫ t in 0..(T : ℝ), deriv a t • valueL2 (functionLip f hf K0 h0) t.toNNReal) +
        (1 / 2 : ℝ) • (∫ t in 0..(T : ℝ), a t • curvatureValue f hf K1 h1 t.toNNReal) := by
  have hda := ha.continuous_deriv (by norm_num)
  have hU := smooth_integrand_continuous f hf K0 K1 h0 h1
  have hJ (t : ℝ≥0) : itoIntegral (integrand (derivativeLip f hf K1 h1) t) =
      valueL2 (functionLip f hf K0 h0) t - valueL2 (functionLip f hf K0 h0) 0 - (1 / 2 : ℝ) • primitive f hf K1 h1 t := by
    have h := c2_ito f hf K0 K1 h0 h1 t
    change _ = _ + (1 / 2 : ℝ) • primitive f hf K1 h1 t at h
    linear_combination (norm := module) -h
  have hiF : IntervalIntegrable (fun t : ℝ => deriv a t • valueL2 (functionLip f hf K0 h0) t.toNNReal) volume 0 T :=
    (hda.smul ((valueL2_continuous (functionLip f hf K0 h0)).comp continuous_real_toNNReal)).intervalIntegrable _ _
  have hi0 : IntervalIntegrable (fun t : ℝ => deriv a t • valueL2 (functionLip f hf K0 h0) 0) volume 0 T :=
    (hda.smul continuous_const).intervalIntegrable _ _
  have hiV : IntervalIntegrable (fun t : ℝ => deriv a t • primitive f hf K1 h1 t) volume 0 T :=
    (hda.smul (primitive_continuous f hf K1 h1)).intervalIntegrable _ _
  have hiV2 : IntervalIntegrable (fun t : ℝ => (1 / 2 : ℝ) • (deriv a t • primitive f hf K1 h1 t)) volume 0 T :=
    hiV.smul (1 / 2 : ℝ)
  have htime : (∫ t in 0..(T : ℝ), deriv a t) = a T - a 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (ha.differentiable (by norm_num) t).hasDerivAt) (hda.intervalIntegrable _ _)
  have hint : (∫ t in 0..(T : ℝ), deriv a t • itoIntegral (integrand (derivativeLip f hf K1 h1) t.toNNReal)) =
      (∫ t in 0..(T : ℝ), deriv a t • valueL2 (functionLip f hf K0 h0) t.toNNReal) -
        (a T - a 0) • valueL2 (functionLip f hf K0 h0) 0 -
        (1 / 2 : ℝ) • (∫ t in 0..(T : ℝ), deriv a t • primitive f hf K1 h1 t) := by
    calc
      _ = ∫ t in 0..(T : ℝ), (deriv a t • valueL2 (functionLip f hf K0 h0) t.toNNReal -
          deriv a t • valueL2 (functionLip f hf K0 h0) 0) - (1 / 2 : ℝ) • (deriv a t • primitive f hf K1 h1 t) := by
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
  have hi := integral_weighted_field (integrand (derivativeLip f hf K1 h1)) hU a (deriv a) hda T
  rw [← weightedField_eq f hf K0 K1 h0 h1 a ha T, hJ, hint] at hi
  have hp := weighted_primitive_identity f hf K1 h1 a ha T
  linear_combination (norm := module) -hi - (1 / 2 : ℝ) • hp


/-- The same formula with the actual time/space generator combined in one
integrable Bochner drift. Both partial derivatives are independently verified below. -/
theorem time_weighted_ito_combined (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a) (T : ℝ≥0) :
    a T • valueL2 (functionLip f hf K0 h0) T - a 0 • valueL2 (functionLip f hf K0 h0) 0 =
      itoIntegral (weightedField a ha.continuous (derivativeLip f hf K1 h1) T) +
        ∫ t in 0..(T : ℝ), deriv a t • valueL2 (functionLip f hf K0 h0) t.toNNReal +
          (1 / 2 : ℝ) • (a t • curvatureValue f hf K1 h1 t.toNNReal) := by
  have hi1 : IntervalIntegrable (fun t : ℝ => deriv a t • valueL2 (functionLip f hf K0 h0) t.toNNReal) volume 0 T :=
    ((ha.continuous_deriv (by norm_num)).smul
      ((valueL2_continuous (functionLip f hf K0 h0)).comp continuous_real_toNNReal)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => a t • curvatureValue f hf K1 h1 t.toNNReal) volume 0 T :=
    (ha.continuous.smul ((curvature_continuous f hf K1 h1).comp continuous_real_toNNReal)).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun t : ℝ => (1 / 2 : ℝ) • (a t • curvatureValue f hf K1 h1 t.toNNReal)) volume 0 T :=
    hi2.smul (1 / 2 : ℝ)
  rw [intervalIntegral.integral_add hi1 hi3, intervalIntegral.integral_smul, ← add_assoc]
  exact time_weighted_ito f hf K0 K1 h0 h1 a ha T


end OperatorDerivativeRewrite.Foundation.GaussianC2TimeWeighted
