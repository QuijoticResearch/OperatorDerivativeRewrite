import Foundation.RightContinuousBoundedSampling
import Foundation.MarkedDynkinMartingale

/-! Actual complex Dynkin identities at bounded stopping times of the natural filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.MarkedDynkinSampling
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedTimeIntegral MarkedDynkinMartingale
open ComplexRootTransitionOperator

theorem rightContinuous (a : ℝ) (f : Test) (ω : StateSample) :
    IsRightContinuous (fun t : ℝ≥0 => dynkin a f t ω) := by
  have ho := (process_rightContinuous a ω).continuous_comp f.continuous
  have hc : IsRightContinuous (fun _ : ℝ≥0 => f 0) := continuous_const.isRightContinuous
  have hp := (primitive_continuous a (generator 1 a f) ω).isRightContinuous
  have he : (fun t : ℝ≥0 => dynkin a f t ω) =
      ((fun t : ℝ≥0 => f (process a t ω))-(fun _ => f 0))-
        (fun t => primitive a (generator 1 a f) t ω) := by funext t; rfl
  rw [he]
  exact (ho.sub hc).sub hp

variable (a : ℝ) (f : Test) (τ : StateSample → ℝ≥0)
  (hτ : IsStoppingTime (history a) (fun ω => (τ ω : WithTop ℝ≥0)))
  (N : ℕ) (hN : ∀ ω, τ ω ≤ N)

include hτ hN in
theorem stopped_integrable : Integrable (fun ω => dynkin a f (τ ω) ω) probability :=
  RightContinuousBoundedSampling.stopped_integrable probability (history a) (dynkin a f)
    (dynkin_martingale a f) (rightContinuous a f) τ hτ N hN

include hτ hN in
theorem stopped_condExp :
    (fun ω => dynkin a f (τ ω) ω) =ᵐ[probability]
      probability[dynkin a f (N : ℝ≥0) | hτ.measurableSpace] :=
  RightContinuousBoundedSampling.stopped_ae_condExp probability (history a) (dynkin a f)
    (dynkin_martingale a f) (rightContinuous a f) τ hτ N hN

include hτ hN in
theorem stopped_mean : (∫ ω, dynkin a f (τ ω) ω ∂probability) = 0 := by
  rw [RightContinuousBoundedSampling.stopped_expectation probability (history a) (dynkin a f)
    (dynkin_martingale a f) (rightContinuous a f) τ hτ N hN,dynkin_mean]

include hτ in
theorem stopped_observable_measurable : Measurable (fun ω => f (process a (τ ω) ω)) := by
  have hm := measurable_stoppedValue (process_progressive a) hτ
  change Measurable[hτ.measurableSpace] (fun ω => process a (τ ω) ω) at hm
  exact (f.continuous.measurable.comp hm).mono hτ.measurableSpace_le le_rfl

include hτ in
theorem stopped_observable_integrable :
    Integrable (fun ω => f (process a (τ ω) ω)) probability := by
  exact Integrable.of_bound (stopped_observable_measurable a f τ hτ).aestronglyMeasurable ‖f‖
    (Eventually.of_forall (fun ω => f.norm_coe_le_norm _))

include hτ in
theorem stopped_primitive_measurable :
    Measurable (fun ω => primitive a (generator 1 a f) (τ ω) ω) := by
  have hu := (primitive_adapted a (generator 1 a f)).isStronglyProgressive_of_continuous
    (primitive_continuous a (generator 1 a f))
  have hm := measurable_stoppedValue hu hτ
  change Measurable[hτ.measurableSpace]
    (fun ω => primitive a (generator 1 a f) (τ ω) ω) at hm
  exact hm.mono hτ.measurableSpace_le le_rfl

include hτ hN in
theorem stopped_primitive_integrable :
    Integrable (fun ω => primitive a (generator 1 a f) (τ ω) ω) probability := by
  have he : (fun ω => primitive a (generator 1 a f) (τ ω) ω) =
      (fun ω => f (process a (τ ω) ω))-(fun _ => f 0)-(fun ω => dynkin a f (τ ω) ω) := by
    funext ω
    simp only [dynkin,Pi.sub_apply]
    ring
  rw [he]
  exact ((stopped_observable_integrable a f τ hτ).sub (integrable_const (f 0))).sub
    (stopped_integrable a f τ hτ N hN)

include hτ hN in
theorem stopped_dynkin_identity :
    (∫ ω, f (process a (τ ω) ω) ∂probability)-f 0 =
      ∫ ω, primitive a (generator 1 a f) (τ ω) ω ∂probability := by
  have hi := stopped_observable_integrable a f τ hτ
  have hd := stopped_primitive_integrable a f τ hτ N hN
  have he : (∫ ω, dynkin a f (τ ω) ω ∂probability) =
      (∫ ω, f (process a (τ ω) ω) ∂probability)-f 0-
        ∫ ω, primitive a (generator 1 a f) (τ ω) ω ∂probability := by
    change (∫ ω, (f (process a (τ ω) ω)-f 0)-
      primitive a (generator 1 a f) (τ ω) ω ∂probability) = _
    have hi0 : Integrable (fun ω => f (process a (τ ω) ω)-f 0) probability :=
      hi.sub (integrable_const (f 0))
    rw [integral_sub hi0 hd,
      integral_sub hi (integrable_const (f 0))]
    simp
  exact sub_eq_zero.mp (he.symm.trans (stopped_mean a f τ hτ N hN))

end OperatorDerivativeRewrite.Foundation.MarkedDynkinSampling
