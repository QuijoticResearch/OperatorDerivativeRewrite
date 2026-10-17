import Foundation.BrownianMassRandomTimeChange
import Foundation.BrownianMassLimitIdentification

/-! Raw-past measurability modulo null sets for the random clock and its
inverse threshold events. This does not assert raw pointwise stopping times. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianMassClockPastEvents
open InfiniteGaussian GaussianTimeProcess BrownianRandomMassClock
open BrownianMassRandomTimeChange BrownianMassLimitIdentification

theorem mass_raw_past (s : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration s] (fun ω => mass ω s) gaussianProduct := by
  have h := continuous_real_toNNReal.comp_aestronglyMeasurable (coordinate_raw_past s)
  apply h.congr
  filter_upwards [mass_agrees] with ω hω
  have he := congrArg Real.toNNReal (hω s)
  simpa only [Real.toNNReal_coe] using he.symm

theorem forward_raw_past (κ s : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration s] (fun ω => forward κ ω s) gaussianProduct :=
  aestronglyMeasurable_const.add (aestronglyMeasurable_const.mul (mass_raw_past s))

theorem inverse_le_iff (κ : ℝ≥0) (ω : SampleSpace) (t s : ℝ≥0) :
    inverse κ ω t ≤ s ↔ t ≤ forward κ ω s :=
  (StickyTimeChangeClock.clockIso κ (mass ω) (mass_continuous ω)
    (mass_monotone ω) (mass_zero ω)).symm_apply_le

theorem inverse_event_raw_version (κ t s : ℝ≥0) :
    ∃ A : Set SampleSpace, MeasurableSet[naturalFiltration s] A ∧
      ∀ᵐ ω ∂gaussianProduct, inverse κ ω t ≤ s ↔ ω ∈ A := by
  obtain ⟨g, hg, he⟩ := forward_raw_past κ s
  refine ⟨{ω | t ≤ g ω}, measurableSet_le measurable_const hg.measurable, ?_⟩
  filter_upwards [he] with ω hω
  change inverse κ ω t ≤ s ↔ t ≤ g ω
  rw [inverse_le_iff, hω]

end OperatorDerivativeRewrite.Foundation.BrownianMassClockPastEvents
