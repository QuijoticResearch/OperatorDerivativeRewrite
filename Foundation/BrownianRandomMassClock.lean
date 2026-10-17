import Foundation.BrownianMassMeasurableKernel
import Foundation.StickyTimeChangeClock

/-! Instantiate the invertible deterministic clock with the actual Brownian
mass, using its centered cumulative function to handle every sample. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianRandomMassClock
open InfiniteGaussian BrownianMassContinuousLimit BrownianMassStieltjesSupport
open BrownianMassMeasurableKernel

def mass (ω : SampleSpace) (t : ℝ≥0) : ℝ≥0 := (cumulative ω t - cumulative ω 0).toNNReal

theorem mass_coe (ω : SampleSpace) (t : ℝ≥0) :
    (mass ω t : ℝ) = cumulative ω t - cumulative ω 0 :=
  Real.coe_toNNReal _ (sub_nonneg.mpr ((cumulative ω).mono t.property))

theorem mass_zero (ω : SampleSpace) : mass ω 0 = 0 := by simp [mass]

theorem mass_monotone (ω : SampleSpace) : Monotone (mass ω) := by
  intro s t hst
  exact Real.toNNReal_mono (sub_le_sub_right ((cumulative ω).mono hst) _)

theorem mass_continuous (ω : SampleSpace) : Continuous (mass ω) :=
  continuous_real_toNNReal.comp ((cumulative_continuous ω).sub continuous_const)

theorem mass_coordinate_measurable (t : ℝ≥0) : Measurable (fun ω => mass ω t) :=
  ((cumulative_coordinate_measurable t).sub (cumulative_coordinate_measurable 0)).real_toNNReal

theorem mass_joint : Measurable (fun z : ℝ≥0 × SampleSpace => mass z.2 z.1) :=
  measurable_uncurry_of_continuous_of_measurable mass_continuous mass_coordinate_measurable

theorem mass_agrees : ∀ᵐ ω ∂gaussianProduct, ∀ t : ℝ≥0, (mass ω t : ℝ) = limitPath ω t := by
  filter_upwards [limitPath_properties] with ω hp t
  rw [mass_coe, cumulative_eq hp.2.1, cumulative_eq hp.2.1, hp.1, sub_zero]

def forward (κ : ℝ≥0) (ω : SampleSpace) : ℝ≥0 → ℝ≥0 :=
  StickyTimeChangeClock.clock κ (mass ω)

theorem forward_continuous (κ : ℝ≥0) (ω : SampleSpace) : Continuous (forward κ ω) :=
  StickyTimeChangeClock.clock_continuous κ _ (mass_continuous ω)

theorem forward_strictMono (κ : ℝ≥0) (ω : SampleSpace) : StrictMono (forward κ ω) :=
  StickyTimeChangeClock.clock_strictMono κ _ (mass_monotone ω)

theorem forward_surjective (κ : ℝ≥0) (ω : SampleSpace) : Function.Surjective (forward κ ω) :=
  StickyTimeChangeClock.clock_surjective κ _ (mass_continuous ω) (mass_zero ω)

theorem forward_zero (κ : ℝ≥0) (ω : SampleSpace) : forward κ ω 0 = 0 := by
  simp [forward, StickyTimeChangeClock.clock, mass_zero]

theorem forward_coordinate_measurable (κ t : ℝ≥0) : Measurable (fun ω => forward κ ω t) :=
  measurable_const.add (measurable_const.mul (mass_coordinate_measurable t))

theorem forward_joint (κ : ℝ≥0) :
    Measurable (fun z : ℝ≥0 × SampleSpace => forward κ z.2 z.1) :=
  measurable_uncurry_of_continuous_of_measurable (forward_continuous κ)
    (forward_coordinate_measurable κ)

end OperatorDerivativeRewrite.Foundation.BrownianRandomMassClock
