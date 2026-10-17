import Foundation.ComplexTiltVariationTest
import Foundation.ComplexRootScaledMoments
import Foundation.MarkedTiltHeatLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! A single fixed bounded continuous test diverges under fourth-order complex tilting. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexTiltVariationDivergence
open ComplexRootHeatTransformLimit

theorem law_phase_source (a ξ η : ℝ) (t : ℝ≥0) :
    (∫ᵛ z, Complex.exp (Complex.I*(η : ℂ)*z)
      ∂[ContinuousLinearMap.mul ℝ ℂ; ComplexRootTiltedLaw.law a ξ t]) =
      ∫ᵛ ω, MarkedHolomorphicExponential.phase a η t ω
        ∂[ContinuousLinearMap.mul ℝ ℂ; MarkedExponentialTilt.source a ξ (fun _ => t)] := by
  have hm : Measurable (fun z : ℂ => Complex.exp (Complex.I*(η : ℂ)*z)) := by fun_prop
  have he := VectorMeasure.integral_map (B := ContinuousLinearMap.mul ℝ ℂ)
    (μ := MarkedExponentialTilt.source a ξ (fun _ => t))
    (f := fun z : ℂ => Complex.exp (Complex.I*(η : ℂ)*z))
    (MarkedRenewalMartingale.process_measurable a t) hm.aestronglyMeasurable
    (MarkedTiltTransform.source_phase_integrable a ξ η t t le_rfl)
  rw [ComplexRootTiltedLaw.own_horizon_coordinate] at he
  exact he

theorem law_holomorphic_limit (T : ℝ≥0) (ξ η : ℝ) :
    Tendsto (fun n : ℕ => ∫ᵛ z, Complex.exp (Complex.I*(η : ℂ)*z)
      ∂[ContinuousLinearMap.mul ℝ ℂ;
        ComplexRootTiltedLaw.law (amplitude 1 n) ξ ((n : ℝ≥0)*T)]) atTop
      (𝓝 ((Real.exp (-(T : ℝ)*((η+ξ)^4-ξ^4)) : ℝ) : ℂ)) := by
  simpa only [law_phase_source] using MarkedTiltHeatLimit.rate_scaled_tilt_limit T T le_rfl ξ η

def growthExponent (T : ℝ≥0) (ξ : ℝ) (n : ℕ) : ℝ :=
  (((n : ℝ≥0)*T : ℝ≥0) : ℝ) * Real.cosh (amplitude 1 n*ξ) *
    (1-Real.cos (amplitude 1 n*ξ))

theorem exponent_atTop (T : ℝ≥0) (hT : 0 < T) (ξ : ℝ) (hξ : ξ ≠ 0) :
    Tendsto (growthExponent T ξ) atTop atTop := by
  have hv := ComplexRootScaledMoments.absolute_second_tendsto 1 (by norm_num)
  have hc : 0 < (T : ℝ)*ξ^2/Real.pi^2 := by positivity
  have hl := hv.const_mul_atTop hc
  have hx := ((amplitude_tendsto 1).mul_const ξ).abs
  simp only [zero_mul, abs_zero] at hx
  have hs : ∀ᶠ n : ℕ in atTop, |amplitude 1 n*ξ| ≤ Real.pi :=
    (hx.eventually (Iio_mem_nhds Real.pi_pos)).mono fun _ hn => hn.le
  refine tendsto_atTop_mono' atTop ?_ hl
  filter_upwards [hs] with n hn
  have hq : (2/Real.pi^2)*(amplitude 1 n*ξ)^2 ≤ 1-Real.cos (amplitude 1 n*ξ) := by
    linarith [Real.cos_le_one_sub_mul_cos_sq hn]
  have hp : 0 ≤ 1-Real.cos (amplitude 1 n*ξ) := sub_nonneg.mpr (Real.cos_le_one _)
  have hb : (2/Real.pi^2)*(amplitude 1 n*ξ)^2 ≤
      Real.cosh (amplitude 1 n*ξ)*(1-Real.cos (amplitude 1 n*ξ)) :=
    hq.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (Real.one_le_cosh (amplitude 1 n*ξ)) hp)
  calc
    _ = ((n : ℝ)*(T : ℝ))*((2/Real.pi^2)*(amplitude 1 n*ξ)^2) := by
      rw [ComplexRootWalkSecondMoment.terminal_absolute_second]
      ring
    _ ≤ ((n : ℝ)*(T : ℝ))*(Real.cosh (amplitude 1 n*ξ)*
        (1-Real.cos (amplitude 1 n*ξ))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = growthExponent T ξ n := by
      simp only [growthExponent, NNReal.coe_mul, NNReal.coe_natCast]
      ring

theorem test_norm_atTop (T : ℝ≥0) (hT : 0 < T) (ξ : ℝ) (hξ : ξ ≠ 0) :
    Tendsto (fun n : ℕ => ‖∫ᵛ z, ComplexTiltVariationTest.test ξ z
      ∂[ContinuousLinearMap.mul ℝ ℂ;
        ComplexRootTiltedLaw.law (amplitude 1 n) ξ ((n : ℝ≥0)*T)]‖) atTop atTop := by
  have he := Real.tendsto_exp_atTop.comp (exponent_atTop T hT ξ hξ)
  simpa only [Function.comp_def, growthExponent, ComplexTiltVariationTest.test_integral,
    Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _)] using he

theorem variation_real_atTop (T : ℝ≥0) (hT : 0 < T) (ξ : ℝ) (hξ : ξ ≠ 0) :
    Tendsto (fun n : ℕ => (ComplexRootTiltedLaw.law (amplitude 1 n) ξ
      ((n : ℝ≥0)*T)).variation.real Set.univ) atTop atTop := by
  have he := Real.tendsto_exp_atTop.comp (exponent_atTop T hT ξ hξ)
  simpa only [Function.comp_def, growthExponent, Measure.real,
    ComplexRootNormTransform.tilted_variation_mass,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] using he

theorem no_fixed_test_limit (T : ℝ≥0) (hT : 0 < T) (ξ : ℝ) (hξ : ξ ≠ 0) (c : ℂ) :
    ¬ Tendsto (fun n : ℕ => ∫ᵛ z, ComplexTiltVariationTest.test ξ z
      ∂[ContinuousLinearMap.mul ℝ ℂ;
        ComplexRootTiltedLaw.law (amplitude 1 n) ξ ((n : ℝ≥0)*T)]) atTop (𝓝 c) := by
  intro h
  have hu : ∀ᶠ n : ℕ in atTop, ‖∫ᵛ z, ComplexTiltVariationTest.test ξ z
      ∂[ContinuousLinearMap.mul ℝ ℂ;
        ComplexRootTiltedLaw.law (amplitude 1 n) ξ ((n : ℝ≥0)*T)]‖ < ‖c‖+1 :=
    h.norm.eventually (Iio_mem_nhds (by linarith))
  have hl := (test_norm_atTop T hT ξ hξ).eventually (eventually_ge_atTop (‖c‖+2))
  obtain ⟨n, hn, hn'⟩ := (hu.and hl).exists
  linarith

theorem no_all_bounded_test_limit (T : ℝ≥0) (hT : 0 < T) (ξ : ℝ) (hξ : ξ ≠ 0)
    (ν : VectorMeasure ℂ ℂ) :
    ¬ ∀ f : ℂ →ᵇ ℂ, Tendsto (fun n : ℕ => ∫ᵛ z, f z
      ∂[ContinuousLinearMap.mul ℝ ℂ;
        ComplexRootTiltedLaw.law (amplitude 1 n) ξ ((n : ℝ≥0)*T)]) atTop
      (𝓝 (∫ᵛ z, f z ∂[ContinuousLinearMap.mul ℝ ℂ; ν])) := by
  intro h
  exact no_fixed_test_limit T hT ξ hξ _ (h (ComplexTiltVariationTest.test ξ))

end OperatorDerivativeRewrite.Foundation.ComplexTiltVariationDivergence
