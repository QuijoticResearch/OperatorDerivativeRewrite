import Foundation.MarkedDynkinSampling
import Foundation.RenewalCompensatedMartingale
import Foundation.BrownianStoppedFourier

/-! Wald identities for bounded stopping times of the genuinely constructed Poisson count. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.RenewalBoundedWald
open ExponentialHoldingSequence (Sample probability)
open RenewalIndependentIncrements RenewalCompensatedMartingale

theorem process_rightContinuous (ω : Sample) :
    IsRightContinuous (fun t : ℝ≥0 => process t ω) := by
  intro t
  have hr := (realPath_cadlag ω).isRightContinuous (t : ℝ)
  exact hr.comp NNReal.continuous_coe.continuousWithinAt (fun r h => h)

theorem compensated_rightContinuous (ω : Sample) :
    IsRightContinuous (fun t : ℝ≥0 => compensated t ω) := by
  have he : (fun t : ℝ≥0 => compensated t ω) =
      (fun t : ℝ≥0 => process t ω)-(fun t : ℝ≥0 => (t : ℝ)) := by funext t; rfl
  rw [he]
  exact (process_rightContinuous ω).sub NNReal.continuous_coe.isRightContinuous

variable (τ : Sample → ℝ≥0)
  (hτ : IsStoppingTime history (fun ω => (τ ω : WithTop ℝ≥0)))
  (N : ℕ) (hN : ∀ ω, τ ω ≤ N)

include hτ in
theorem stopped_time_measurable : Measurable (fun ω => ((τ ω : ℝ≥0) : ℝ)) :=
  measurable_coe_nnreal_real.comp
    ((BrownianStoppedFourier.time_measurable history τ hτ).mono hτ.measurableSpace_le le_rfl)

include hτ hN in
theorem stopped_time_integrable : Integrable (fun ω => ((τ ω : ℝ≥0) : ℝ)) probability := by
  apply Integrable.of_bound (stopped_time_measurable τ hτ).aestronglyMeasurable (N : ℝ)
  filter_upwards with ω
  rw [Real.norm_eq_abs,abs_of_nonneg (τ ω).coe_nonneg]
  exact_mod_cast hN ω

include hτ hN in
theorem stopped_compensated_integrable :
    Integrable (fun ω => compensated (τ ω) ω) probability :=
  RightContinuousBoundedSampling.stopped_integrable probability history compensated
    compensated_martingale compensated_rightContinuous τ hτ N hN

include hτ hN in
theorem stopped_count_integrable : Integrable (fun ω => process (τ ω) ω) probability := by
  have he : (fun ω => process (τ ω) ω) =
      (fun ω => compensated (τ ω) ω)+(fun ω => ((τ ω : ℝ≥0) : ℝ)) := by
    funext ω
    simp only [compensated,Pi.add_apply]
    ring
  rw [he]
  exact (stopped_compensated_integrable τ hτ N hN).add (stopped_time_integrable τ hτ N hN)

include hτ hN in
theorem stopped_compensated_mean : (∫ ω, compensated (τ ω) ω ∂probability) = 0 := by
  have he := RightContinuousBoundedSampling.stopped_expectation probability history compensated
    compensated_martingale compensated_rightContinuous τ hτ N hN
  rw [he]
  change (∫ ω, process (N : ℝ≥0) ω-(N : ℝ) ∂probability) = 0
  rw [integral_sub (process_integrable (N : ℝ≥0)) (integrable_const (N : ℝ)),process_mean]
  simp

include hτ hN in
theorem wald_identity :
    (∫ ω, process (τ ω) ω ∂probability) = ∫ ω, ((τ ω : ℝ≥0) : ℝ) ∂probability := by
  have he := integral_sub (stopped_count_integrable τ hτ N hN) (stopped_time_integrable τ hτ N hN)
  change (∫ ω, compensated (τ ω) ω ∂probability) =
    (∫ ω, process (τ ω) ω ∂probability)-(∫ ω, ((τ ω : ℝ≥0) : ℝ) ∂probability) at he
  exact sub_eq_zero.mp (he.symm.trans (stopped_compensated_mean τ hτ N hN))

include hτ hN in
theorem conditional_wald (σ : Sample → ℝ≥0)
    (hσ : IsStoppingTime history (fun ω => (σ ω : WithTop ℝ≥0))) (hστ : ∀ ω, σ ω ≤ τ ω) :
    probability[fun ω => process (τ ω) ω | hσ.measurableSpace] =ᵐ[probability]
      fun ω => probability[fun ω => ((τ ω : ℝ≥0) : ℝ) | hσ.measurableSpace] ω+
        process (σ ω) ω-(σ ω : ℝ) := by
  have he := condExp_sub (stopped_count_integrable τ hτ N hN)
    (stopped_time_integrable τ hτ N hN) hσ.measurableSpace
  have hf : (fun ω => compensated (τ ω) ω) =
      (fun ω => process (τ ω) ω)-(fun ω => ((τ ω : ℝ≥0) : ℝ)) := rfl
  rw [← hf] at he
  have hs := RightContinuousBoundedSampling.sample_two probability history compensated
    compensated_martingale compensated_rightContinuous τ hτ N hN σ hσ hστ
  filter_upwards [he,hs] with ω he hs
  have hh := he.symm.trans hs
  change probability[fun ω => process (τ ω) ω | hσ.measurableSpace] ω-
    probability[fun ω => ((τ ω : ℝ≥0) : ℝ) | hσ.measurableSpace] ω =
      process (σ ω) ω-(σ ω : ℝ) at hh
  linarith

end OperatorDerivativeRewrite.Foundation.RenewalBoundedWald
