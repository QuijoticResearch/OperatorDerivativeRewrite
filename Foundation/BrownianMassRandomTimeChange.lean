import Foundation.BrownianRandomMassClock

/-! A measurable inverse of the actual random mass clock and its continuous
Brownian time change. No Markov, sticky generator or flow law is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianMassRandomTimeChange
open InfiniteGaussian IBMConstructedSources BrownianRandomMassClock BrownianMassContinuousLimit

def inverse (κ : ℝ≥0) (ω : SampleSpace) : ℝ≥0 → ℝ≥0 :=
  StickyTimeChangeClock.inverseClock κ (mass ω) (mass_continuous ω) (mass_monotone ω) (mass_zero ω)

theorem forward_inverse (κ : ℝ≥0) (ω : SampleSpace) (t : ℝ≥0) :
    forward κ ω (inverse κ ω t) = t :=
  StickyTimeChangeClock.clock_inverse κ _ _ _ _ t

theorem inverse_forward (κ : ℝ≥0) (ω : SampleSpace) (s : ℝ≥0) :
    inverse κ ω (forward κ ω s) = s :=
  StickyTimeChangeClock.inverse_clock κ _ _ _ _ s

theorem inverse_continuous (κ : ℝ≥0) (ω : SampleSpace) : Continuous (inverse κ ω) :=
  StickyTimeChangeClock.inverse_continuous κ _ _ _ _

theorem inverse_monotone (κ : ℝ≥0) (ω : SampleSpace) : Monotone (inverse κ ω) :=
  StickyTimeChangeClock.inverse_monotone κ _ _ _ _

theorem inverse_le (κ : ℝ≥0) (ω : SampleSpace) (t : ℝ≥0) : inverse κ ω t ≤ t :=
  StickyTimeChangeClock.inverse_le κ _ _ _ _ t

theorem inverse_increment (κ : ℝ≥0) (ω : SampleSpace) (s t : ℝ≥0) (hst : s ≤ t) :
    (inverse κ ω t : ℝ) - inverse κ ω s ≤ (t : ℝ) - s :=
  StickyTimeChangeClock.inverse_increment κ _ _ _ _ s t hst

theorem inverse_zero (κ : ℝ≥0) (ω : SampleSpace) : inverse κ ω 0 = 0 := by
  have h := inverse_forward κ ω 0
  rwa [forward_zero] at h

theorem inverse_lt_iff (κ : ℝ≥0) (ω : SampleSpace) (t b : ℝ≥0) :
    inverse κ ω t < b ↔ t < forward κ ω b :=
  (StickyTimeChangeClock.clockIso κ (mass ω) (mass_continuous ω)
    (mass_monotone ω) (mass_zero ω)).symm_apply_lt

theorem inverse_coordinate_measurable (κ t : ℝ≥0) : Measurable (fun ω => inverse κ ω t) := by
  apply measurable_of_Iio
  intro b
  have he : {ω | inverse κ ω t < b} = {ω | t < forward κ ω b} := by
    ext ω
    exact inverse_lt_iff κ ω t b
  change MeasurableSet {ω | inverse κ ω t < b}
  rw [he]
  exact measurableSet_lt measurable_const (forward_coordinate_measurable κ b)

theorem inverse_joint (κ : ℝ≥0) :
    Measurable (fun z : ℝ≥0 × SampleSpace => inverse κ z.2 z.1) :=
  measurable_uncurry_of_continuous_of_measurable (inverse_continuous κ)
    (inverse_coordinate_measurable κ)

def inversePath (κ : ℝ≥0) (ω : SampleSpace) : C(ℝ≥0, ℝ≥0) :=
  ⟨inverse κ ω, inverse_continuous κ ω⟩

theorem inversePath_measurable (κ : ℝ≥0) : Measurable (inversePath κ) :=
  ContinuousMap.measurable_iff_eval.mpr (inverse_coordinate_measurable κ)

def changedPath (κ : ℝ≥0) (ω : SampleSpace) : C(ℝ≥0, ℝ) :=
  (clockPath ω).comp (inversePath κ ω)

theorem changedPath_coordinate_measurable (κ t : ℝ≥0) :
    Measurable (fun ω => changedPath κ ω t) :=
  continuous_eval.measurable.comp (clockPath_measurable.prodMk (inverse_coordinate_measurable κ t))

theorem changedPath_measurable (κ : ℝ≥0) : Measurable (changedPath κ) :=
  ContinuousMap.measurable_iff_eval.mpr (changedPath_coordinate_measurable κ)

theorem changedPath_joint (κ : ℝ≥0) :
    Measurable (fun z : ℝ≥0 × SampleSpace => changedPath κ z.2 z.1) :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => (changedPath κ ω).continuous)
    (changedPath_coordinate_measurable κ)

theorem inverse_balance (κ : ℝ≥0) (ω : SampleSpace) (t : ℝ≥0) :
    (inverse κ ω t : ℝ) + (κ : ℝ) * mass ω (inverse κ ω t) = (t : ℝ) := by
  have h := congrArg (fun u : ℝ≥0 => (u : ℝ)) (forward_inverse κ ω t)
  simpa only [forward, StickyTimeChangeClock.clock, NNReal.coe_add, NNReal.coe_mul] using h

theorem balance_with_limit (κ : ℝ≥0) : ∀ᵐ ω ∂gaussianProduct, ∀ t : ℝ≥0,
    (inverse κ ω t : ℝ) + (κ : ℝ) * limitPath ω (inverse κ ω t) = (t : ℝ) := by
  filter_upwards [mass_agrees] with ω hω t
  have h := inverse_balance κ ω t
  rwa [hω] at h

theorem recover_original (κ : ℝ≥0) (ω : SampleSpace) (s : ℝ≥0) :
    changedPath κ ω (forward κ ω s) = clockPath ω s := by
  change clockPath ω (inverse κ ω (forward κ ω s)) = _
  rw [inverse_forward]

theorem inverse_parameter_zero (ω : SampleSpace) (t : ℝ≥0) : inverse 0 ω t = t := by
  have h := forward_inverse 0 ω t
  simpa only [forward, StickyTimeChangeClock.clock, zero_mul, add_zero] using h

theorem changedPath_parameter_zero (ω : SampleSpace) : changedPath 0 ω = clockPath ω := by
  ext t
  change clockPath ω (inverse 0 ω t) = clockPath ω t
  rw [inverse_parameter_zero]

end OperatorDerivativeRewrite.Foundation.BrownianMassRandomTimeChange
