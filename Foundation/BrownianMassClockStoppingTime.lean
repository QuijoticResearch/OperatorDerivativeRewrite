import Foundation.AmbientNullAugmentation
import Foundation.BrownianMassClockPastEvents
import Mathlib.Probability.Process.Stopping

/-! The constructed inverse clock is a genuine stopping time for an explicit
ambient null augmentation. No usual-conditions or Markov theorem assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianMassClockStoppingTime
open InfiniteGaussian GaussianTimeProcess BrownianRandomMassClock
open BrownianMassRandomTimeChange BrownianMassClockPastEvents AmbientNullAugmentation

def augmentedPast : Filtration ℝ≥0 (inferInstance : MeasurableSpace SampleSpace) :=
  filtration gaussianProduct naturalFiltration

theorem raw_le_augmented (s : ℝ≥0) : naturalFiltration s ≤ augmentedPast s :=
  filtration_raw_le gaussianProduct naturalFiltration s

theorem mass_measurable_past (s : ℝ≥0) :
    Measurable[augmentedPast s] (fun ω => mass ω s) :=
  measurable_of_raw_aestronglyMeasurable (naturalFiltration s) gaussianProduct
    (mass_coordinate_measurable s)
    (mass_raw_past s)

theorem forward_measurable_past (κ s : ℝ≥0) :
    Measurable[augmentedPast s] (fun ω => forward κ ω s) :=
  measurable_of_raw_aestronglyMeasurable (naturalFiltration s) gaussianProduct
    (forward_coordinate_measurable κ s)
    (forward_raw_past κ s)

theorem mass_stronglyAdapted : StronglyAdapted augmentedPast (fun s ω => mass ω s) :=
  fun s => (mass_measurable_past s).stronglyMeasurable

theorem forward_stronglyAdapted (κ : ℝ≥0) :
    StronglyAdapted augmentedPast (fun s ω => forward κ ω s) :=
  fun s => (forward_measurable_past κ s).stronglyMeasurable

theorem inverse_isStoppingTime (κ t : ℝ≥0) :
    IsStoppingTime augmentedPast (fun ω => (inverse κ ω t : WithTop ℝ≥0)) := by
  intro s
  have h : MeasurableSet[augment (naturalFiltration s) gaussianProduct]
      {ω | inverse κ ω t ≤ s} :=
    ⟨measurableSet_le (inverse_coordinate_measurable κ t) measurable_const,
      inverse_event_raw_version κ t s⟩
  simpa only [WithTop.coe_le_coe] using h

theorem inverse_stopping_bounded (κ t : ℝ≥0) (ω : SampleSpace) :
    (inverse κ ω t : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) := by
  simpa only [WithTop.coe_le_coe] using inverse_le κ ω t

theorem condExp_unchanged (s : ℝ≥0) (F : SampleSpace → ℝ) (hF : Integrable F gaussianProduct) :
    gaussianProduct[F | naturalFiltration s] =ᵐ[gaussianProduct]
      gaussianProduct[F | augmentedPast s] :=
  condExp_invariant (naturalFiltration s) gaussianProduct (naturalFiltration.le s) F hF

end OperatorDerivativeRewrite.Foundation.BrownianMassClockStoppingTime
