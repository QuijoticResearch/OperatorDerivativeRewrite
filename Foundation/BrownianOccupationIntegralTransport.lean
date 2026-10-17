import Foundation.BrownianTimeChangedOccupationMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Actual bounded continuous spatial observations under the clock transport.
The holding term is retained explicitly in physical-time integrals. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianOccupationIntegralTransport
open InfiniteGaussian IBMConstructedSources BrownianRandomMassClock BrownianMassRandomTimeChange
open BrownianClockMeasureTransport BrownianTimeChangedOccupationMeasure
set_option backward.isDefEq.respectTransparency false

theorem ordinaryTime_restrict (T : ℝ≥0) :
    ordinaryTime.restrict (Iic T) =
      Measure.map Real.toNNReal ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))) := by
  rw [ordinaryTime, Measure.restrict_map continuous_real_toNNReal.measurable measurableSet_Iic,
    Measure.restrict_restrict (measurableSet_Iic.preimage continuous_real_toNNReal.measurable),
    positive_preimage_Iic]

theorem ordinaryTime_integral (h : ℝ≥0 → ℝ) (hc : Continuous h) (T : ℝ≥0) :
    (∫ t in Iic T, h t ∂ordinaryTime) = ∫ s in 0..(T : ℝ), h s.toNNReal := by
  rw [ordinaryTime_restrict, integral_map continuous_real_toNNReal.measurable.aemeasurable
    hc.stronglyMeasurable.aestronglyMeasurable, intervalIntegral.integral_of_le T.coe_nonneg]

theorem bounded_observation_transport (g : ℝ → ℝ) (hg : Continuous g) (K : ℝ)
    (hK : ∀ x, ‖g x‖ ≤ K) : ∀ᵐ ω ∂gaussianProduct, ∀ κ T : ℝ≥0,
    (∫ s in 0..(T : ℝ), g (changedPath κ ω s.toNNReal)) =
      (∫ s in 0..(inverse κ ω T : ℝ), g (clockPath ω s.toNNReal))+
        (κ : ℝ)*(mass ω (inverse κ ω T) : ℝ)*g 0 := by
  filter_upwards [occupation_decomposition] with ω hω κ T
  let A := inverse κ ω T
  let c : ℝ≥0∞ := (κ : ℝ≥0∞)*(mass ω A : ℝ≥0∞)
  letI : IsFiniteMeasure (originalOccupation ω A) := ⟨by
    rw [originalOccupation_total]
    exact ENNReal.coe_lt_top⟩
  have hi : Integrable g (originalOccupation ω A) := by
    exact (integrable_const K).mono' hg.stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall hK)
  have hd : Integrable g (c • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
  have he : (∫ x, g x ∂changedOccupation κ ω T) =
      (∫ x, g x ∂originalOccupation ω A)+c.toReal*g 0 := by
    rw [hω κ T, integral_add_measure hi hd, integral_smul_measure, integral_dirac]
    rfl
  rw [changedOccupation, originalOccupation,
    integral_map (changedPath κ ω).continuous.measurable.aemeasurable
      hg.stronglyMeasurable.aestronglyMeasurable,
    integral_map (clockPath ω).continuous.measurable.aemeasurable
      hg.stronglyMeasurable.aestronglyMeasurable,
    ordinaryTime_integral (fun s => g (changedPath κ ω s)) (hg.comp (changedPath κ ω).continuous) T,
    ordinaryTime_integral (fun s => g (clockPath ω s)) (hg.comp (clockPath ω).continuous) A] at he
  simpa only [c, ENNReal.toReal_mul, ENNReal.coe_toReal, smul_eq_mul, A] using he

end OperatorDerivativeRewrite.Foundation.BrownianOccupationIntegralTransport
