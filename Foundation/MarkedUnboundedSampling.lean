import Foundation.RenewalBoundedWald
import Foundation.MarkedQuarticCompensation
import Foundation.MarkedExponentialMartingale

/-! Genuine unbounded quartic and exponential identities at bounded stopping times. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MarkedUnboundedSampling
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedTimeIntegral MarkedHolomorphicExponential
open MarkedQuarticCompensation MarkedExponentialMartingale

theorem quartic_rightContinuous (a : ℝ) (ω : StateSample) :
    IsRightContinuous (fun t : ℝ≥0 => compensated a t ω) := by
  have hp := (process_rightContinuous a ω).continuous_comp
    (show Continuous (fun z : ℂ => z^4) by fun_prop)
  have ht : Continuous (fun t : ℝ≥0 => 4*(t : ℂ)*(a : ℂ)^4) := by fun_prop
  have he : (fun t : ℝ≥0 => compensated a t ω) =
      (fun t : ℝ≥0 => process a t ω^4)+(fun t : ℝ≥0 => 4*(t : ℂ)*(a : ℂ)^4) := by
    funext t
    rfl
  rw [he]
  exact hp.add ht.isRightContinuous

theorem exponential_rightContinuous (a ξ : ℝ) (ω : StateSample) :
    IsRightContinuous (fun t : ℝ≥0 => normalized a ξ t ω) := by
  have hp : IsRightContinuous (fun t : ℝ≥0 => phase a ξ t ω) := by
    change IsRightContinuous ((fun z : ℂ => Complex.exp (Complex.I*(ξ : ℂ)*z)) ∘
      (fun t : ℝ≥0 => process a t ω))
    exact (process_rightContinuous a ω).continuous_comp (by fun_prop)
  have ht : Continuous (fun t : ℝ≥0 => Complex.exp (-(t : ℂ)*symbol a ξ)) := by fun_prop
  have he : (fun t : ℝ≥0 => normalized a ξ t ω) =
      (fun t : ℝ≥0 => Complex.exp (-(t : ℂ)*symbol a ξ))*(fun t => phase a ξ t ω) := by
    funext t
    rfl
  rw [he]
  exact ht.isRightContinuous.mul hp

theorem quartic_mean (a : ℝ) (t : ℝ≥0) : (∫ ω, compensated a t ω ∂probability) = 0 := by
  have hz : compensated a 0 = (fun _ : StateSample => (0 : ℂ)) := by
    funext ω
    simp [compensated,process,MarkedRootRenewalProcess.process_zero]
  calc
    _ = ∫ ω, probability[compensated a t | history a 0] ω ∂probability :=
      (integral_condExp ((history a).le 0)).symm
    _ = ∫ ω, compensated a 0 ω ∂probability :=
      integral_congr_ae (compensated_condExp a 0 t bot_le)
    _ = 0 := by rw [hz]; simp

variable (a : ℝ) (τ : StateSample → ℝ≥0)
  (hτ : IsStoppingTime (history a) (fun ω => (τ ω : WithTop ℝ≥0)))
  (N : ℕ) (hN : ∀ ω, τ ω ≤ N)

include hτ hN in
theorem quartic_stopped_integrable : Integrable (fun ω => compensated a (τ ω) ω) probability :=
  RightContinuousBoundedSampling.stopped_integrable probability (history a) (compensated a)
    (compensated_martingale a) (quartic_rightContinuous a) τ hτ N hN

include hτ hN in
theorem quartic_stopped_mean : (∫ ω, compensated a (τ ω) ω ∂probability) = 0 := by
  rw [RightContinuousBoundedSampling.stopped_expectation probability (history a) (compensated a)
    (compensated_martingale a) (quartic_rightContinuous a) τ hτ N hN,quartic_mean]

include hτ hN in
theorem stopped_time_integrable : Integrable (fun ω => ((τ ω : ℝ≥0) : ℝ)) probability := by
  have hm : Measurable (fun ω => ((τ ω : ℝ≥0) : ℝ)) := measurable_coe_nnreal_real.comp
    ((BrownianStoppedFourier.time_measurable (history a) τ hτ).mono hτ.measurableSpace_le le_rfl)
  apply Integrable.of_bound hm.aestronglyMeasurable (N : ℝ)
  filter_upwards with ω
  rw [Real.norm_eq_abs,abs_of_nonneg (τ ω).coe_nonneg]
  exact_mod_cast hN ω

include hτ hN in
theorem stopped_quartic_integrable :
    Integrable (fun ω => process a (τ ω) ω^4) probability := by
  have ht := stopped_time_integrable a τ hτ N hN
  have hc : Integrable (fun ω => (4*(a : ℂ)^4)*((τ ω : ℝ) : ℂ)) probability :=
    ht.ofReal.const_mul _
  have he : (fun ω => process a (τ ω) ω^4) =
      (fun ω => compensated a (τ ω) ω)-(fun ω => (4*(a : ℂ)^4)*((τ ω : ℝ) : ℂ)) := by
    funext ω
    simp only [compensated,Pi.sub_apply]
    ring
  rw [he]
  exact (quartic_stopped_integrable a τ hτ N hN).sub hc

include hτ hN in
theorem stopped_quartic_identity :
    (∫ ω, process a (τ ω) ω^4 ∂probability) =
      -4*Complex.ofReal (∫ ω, ((τ ω : ℝ≥0) : ℝ) ∂probability)*(a : ℂ)^4 := by
  have ht := stopped_time_integrable a τ hτ N hN
  have hc : Integrable (fun ω => (4*(a : ℂ)^4)*((τ ω : ℝ) : ℂ)) probability :=
    ht.ofReal.const_mul _
  have hm : (∫ ω, process a (τ ω) ω^4+(4*(a : ℂ)^4)*((τ ω : ℝ) : ℂ) ∂probability) = 0 := by
    have he : (fun ω => process a (τ ω) ω^4+(4*(a : ℂ)^4)*((τ ω : ℝ) : ℂ)) =
        (fun ω => compensated a (τ ω) ω) := by
      funext ω
      simp only [compensated]
      ring
    rw [he]
    exact quartic_stopped_mean a τ hτ N hN
  rw [integral_add (stopped_quartic_integrable a τ hτ N hN) hc,integral_const_mul,
    integral_complex_ofReal] at hm
  calc
    _ = -((4*(a : ℂ)^4)*Complex.ofReal (∫ ω, ((τ ω : ℝ≥0) : ℝ) ∂probability)) :=
      eq_neg_of_add_eq_zero_left hm
    _ = _ := by ring

include hτ hN in
theorem exponential_stopped_integrable (ξ : ℝ) :
    Integrable (fun ω => normalized a ξ (τ ω) ω) probability :=
  RightContinuousBoundedSampling.stopped_integrable probability (history a) (normalized a ξ)
    (normalized_martingale a ξ) (exponential_rightContinuous a ξ) τ hτ N hN

include hτ hN in
theorem exponential_stopped_mean (ξ : ℝ) :
    (∫ ω, normalized a ξ (τ ω) ω ∂probability) = 1 := by
  rw [RightContinuousBoundedSampling.stopped_expectation probability (history a) (normalized a ξ)
    (normalized_martingale a ξ) (exponential_rightContinuous a ξ) τ hτ N hN,normalized_mean]

include hτ hN in
theorem exponential_stopped_condExp (ξ : ℝ) :
    (fun ω => normalized a ξ (τ ω) ω) =ᵐ[probability]
      probability[normalized a ξ (N : ℝ≥0) | hτ.measurableSpace] :=
  RightContinuousBoundedSampling.stopped_ae_condExp probability (history a) (normalized a ξ)
    (normalized_martingale a ξ) (exponential_rightContinuous a ξ) τ hτ N hN

end OperatorDerivativeRewrite.Foundation.MarkedUnboundedSampling
