import Foundation.ExponentialResponseTimeIntegral
import Foundation.GaussianVolterraMartingaleRepair

/-! The actual OU convolution satisfies a Bochner-L2 drift balance with the
constructed Brownian motion. No sample-path semimartingale theorem is inferred. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianVolterraDriftBalance
set_option backward.isDefEq.respectTransparency false
open InfiniteGaussian GaussianTimeHilbert GaussianHilbertProcess
open GaussianExponentialMarkovPrediction SPDEExponentialForcing
open ExponentialResponseTimeIntegral
attribute [local instance] timeHilbert_secondCountable

theorem value_eq_isonormal (rate t : ℝ≥0) :
    value rate t = isonormalEmbedding TimeHilbert (responseVector rate t) := rfl

theorem value_continuous (rate : ℝ≥0) (hr : 0 < rate) : Continuous (value rate) :=
  (isonormalEmbedding TimeHilbert).continuous.comp
    (SPDEExponentialTimeContinuity.responseVector_continuous rate hr)

def primitive (rate : ℝ≥0) (t : ℝ) : GaussianL2 :=
  ∫ s in 0..t, value rate s.toNNReal

theorem value_intervalIntegrable (rate : ℝ≥0) (hr : 0 < rate) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => value rate s.toNNReal) volume a b :=
  ((value_continuous rate hr).comp continuous_real_toNNReal).intervalIntegrable _ _

theorem primitive_derivative (rate : ℝ≥0) (hr : 0 < rate) (t : ℝ) :
    HasDerivAt (primitive rate) (value rate t.toNNReal) t := by
  have hc := (value_continuous rate hr).comp continuous_real_toNNReal
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem primitive_exact (rate T : ℝ≥0) (hr : 0 < rate) :
    primitive rate T = (rate : ℝ)⁻¹ • (GaussianTimeProcess.wienerL2 T-value rate T) := by
  let L := (isonormalEmbedding TimeHilbert).toContinuousLinearMap
  calc
    primitive rate T = ∫ s in 0..(T : ℝ), L (responseVector rate s.toNNReal) := rfl
    _ = L (∫ s in 0..(T : ℝ), responseVector rate s.toNNReal) :=
      L.intervalIntegral_comp_comm (profile_intervalIntegrable rate T hr)
    _ = _ := by
      rw [integral_responseVector rate T hr]
      change isonormalEmbedding TimeHilbert
        ((rate : ℝ)⁻¹ • (timeVector T-responseVector rate T)) = _
      rw [map_smul, map_sub]
      rfl

theorem drift_balance (rate T : ℝ≥0) (hr : 0 < rate) :
    value rate T+(rate : ℝ) • primitive rate T = GaussianTimeProcess.wienerL2 T := by
  rw [primitive_exact rate T hr, smul_smul,
    mul_inv_cancel₀ (show (rate : ℝ) ≠ 0 from ne_of_gt hr), one_smul]
  abel

def driftPrimitive (rate : ℝ≥0) (t : ℝ) : GaussianL2 := -(rate : ℝ) • primitive rate t

theorem drift_derivative (rate : ℝ≥0) (hr : 0 < rate) (t : ℝ) :
    HasDerivAt (driftPrimitive rate) (-(rate : ℝ) • value rate t.toNNReal) t := by
  exact (primitive_derivative rate hr t).const_smul (-(rate : ℝ))

theorem drift_derivative_norm_sq (rate T : ℝ≥0) (hr : 0 < rate) :
    ‖deriv (driftPrimitive rate) (T : ℝ)‖^2 =
      (rate : ℝ)*(1-Real.exp (-2*(rate : ℝ)*(T : ℝ)))/2 := by
  rw [(drift_derivative rate hr T).deriv, Real.toNNReal_coe, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, GaussianVolterraMartingaleObstruction.value_norm_sq rate T hr]
  field_simp [(show (rate : ℝ) ≠ 0 from ne_of_gt hr)] <;> ring

theorem drift_derivative_nonzero (rate T : ℝ≥0) (hr : 0 < rate) (hT : 0 < T) :
    deriv (driftPrimitive rate) (T : ℝ) ≠ 0 := by
  have he : Real.exp (-2*(rate : ℝ)*(T : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by
    have hr' : 0 < (rate : ℝ) := hr
    have hT' : 0 < (T : ℝ) := hT
    nlinarith)
  have hp : 0 < (rate : ℝ)*(1-Real.exp (-2*(rate : ℝ)*(T : ℝ)))/2 := by
    have hr' : 0 < (rate : ℝ) := hr
    positivity
  rw [← drift_derivative_norm_sq rate T hr] at hp
  intro hz
  rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hp
  exact lt_irrefl _ hp

theorem original_noise_plus_drift (rate T : ℝ≥0) (hr : 0 < rate) :
    value rate T = GaussianTimeProcess.wienerL2 T+driftPrimitive rate T := by
  have h := drift_balance rate T hr
  unfold driftPrimitive
  rw [neg_smul]
  linear_combination (norm := module) h

theorem compensated_is_brownian (rate T : ℝ≥0) (hr : 0 < rate) :
    value rate T-driftPrimitive rate T = GaussianTimeProcess.wienerL2 T := by
  rw [original_noise_plus_drift rate T hr, add_sub_cancel_right]

theorem zero_rate_value (T : ℝ≥0) : value 0 T = GaussianTimeProcess.wienerL2 T := by
  have he : responseVector 0 T = timeVector T := by
    apply Lp.ext
    filter_upwards [responseVector_coeFn 0 T, timeVector_coeFn T] with u hu ht
    rw [hu, ht]
    simp [response]
  rw [value_eq_isonormal, he]
  rfl

end OperatorDerivativeRewrite.Foundation.GaussianVolterraDriftBalance
