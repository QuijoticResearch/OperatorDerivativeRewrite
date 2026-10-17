import Foundation.ContinuousTimeChangeMartingale
import Foundation.BrownianAugmentedMartingales
import Foundation.BrownianStickyOccupation

/-! Genuine martingales for the already constructed random Brownian mass
clock. This does not assert transition kernels, a generator, or a stochastic flow. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianTimeChangedMartingales
open InfiniteGaussian IBMConstructedSources BrownianMassContinuousLimit
open BrownianRandomMassClock BrownianMassRandomTimeChange BrownianMassClockStoppingTime
open BrownianAugmentedMartingales ContinuousTimeChangeMartingale
set_option backward.isDefEq.respectTransparency false

def physicalPast (κ : ℝ≥0) : Filtration ℝ≥0 (inferInstance : MeasurableSpace SampleSpace) :=
  changedFiltration augmentedPast (fun t ω => inverse κ ω t)
    (inverse_isStoppingTime κ) (fun ω => inverse_monotone κ ω)

theorem changed_brownian_martingale (κ : ℝ≥0) :
    Martingale (fun t ω => changedPath κ ω t) (physicalPast κ) gaussianProduct :=
  changed_martingale gaussianProduct augmentedPast (fun t ω => clockPath ω t)
    (fun t ω => inverse κ ω t) (inverse_isStoppingTime κ) (fun ω => inverse_monotone κ ω)
    brownian_martingale (fun ω => (clockPath ω).continuous) (fun t ω => inverse_le κ ω t)

def changedSignPath (κ : ℝ≥0) (ω : SampleSpace) : C(ℝ≥0, ℝ) :=
  (signIntegralPath ω).comp (inversePath κ ω)

theorem changed_sign_martingale (κ : ℝ≥0) :
    Martingale (fun t ω => changedSignPath κ ω t) (physicalPast κ) gaussianProduct :=
  changed_martingale gaussianProduct augmentedPast (fun t ω => signIntegralPath ω t)
    (fun t ω => inverse κ ω t) (inverse_isStoppingTime κ) (fun ω => inverse_monotone κ ω)
    signIntegral_martingale (fun ω => (signIntegralPath ω).continuous) (fun t ω => inverse_le κ ω t)

theorem signIntegralPath_measurable : Measurable signIntegralPath :=
  ContinuousMap.measurable_iff_eval.mpr signIntegral_coordinate_measurable

theorem changedSignPath_measurable (κ : ℝ≥0) : Measurable (changedSignPath κ) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact continuous_eval.measurable.comp
    (signIntegralPath_measurable.prodMk (inverse_coordinate_measurable κ t))

theorem changedSignPath_joint (κ : ℝ≥0) :
    Measurable (fun z : ℝ≥0 × SampleSpace => changedSignPath κ z.2 z.1) :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => (changedSignPath κ ω).continuous)
    (fun t => (ContinuousMap.measurable_eval t).comp (changedSignPath_measurable κ))

def compensator (κ : ℝ≥0) (t : ℝ≥0) (ω : SampleSpace) : ℝ :=
  mass ω (inverse κ ω t)

theorem compensator_nonnegative (κ t : ℝ≥0) (ω : SampleSpace) : 0 ≤ compensator κ t ω :=
  NNReal.coe_nonneg _

theorem compensator_monotone (κ : ℝ≥0) (ω : SampleSpace) :
    Monotone (fun t => compensator κ t ω) := by
  intro s t hst
  exact_mod_cast mass_monotone ω (inverse_monotone κ ω hst)

theorem tanaka_physical (κ : ℝ≥0) : ∀ᵐ ω ∂gaussianProduct, ∀ t : ℝ≥0,
    |changedPath κ ω t| = changedSignPath κ ω t+compensator κ t ω := by
  filter_upwards [mass_agrees] with ω hω t
  have h := tanaka_all ω (inverse κ ω t)
  change |clockPath ω (inverse κ ω t)| = signIntegralPath ω (inverse κ ω t)+_ at h ⊢
  simpa only [compensator, hω] using h

theorem compensator_balance (κ t : ℝ≥0) (ω : SampleSpace) :
    (κ : ℝ)*compensator κ t ω = (t : ℝ)-inverse κ ω t := by
  have h := inverse_balance κ ω t
  change (inverse κ ω t : ℝ)+(κ : ℝ)*compensator κ t ω = t at h
  linarith

theorem compensator_integrable (κ t : ℝ≥0) : Integrable (compensator κ t) gaussianProduct := by
  have hi := ((changed_brownian_martingale κ).integrable t).abs.sub
    ((changed_sign_martingale κ).integrable t)
  apply hi.congr
  filter_upwards [tanaka_physical κ] with ω hω
  have h := hω t
  change |changedPath κ ω t|-changedSignPath κ ω t = compensator κ t ω
  linarith

end OperatorDerivativeRewrite.Foundation.BrownianTimeChangedMartingales
