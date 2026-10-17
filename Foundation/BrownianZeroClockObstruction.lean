import Foundation.BrownianZeroOccupation
import Foundation.StickyTimeChangeClock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! A Lebesgue-density clock supported on Brownian zeros is trivial. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianZeroClockObstruction
open InfiniteGaussian IBMConstructedSources BrownianZeroOccupation

def supportedAtZero (ω : SampleSpace) (q : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → clockPath ω t.toNNReal ≠ 0 → q t = 0

def mass (q : ℝ → ℝ) (T : ℝ≥0) : ℝ := ∫ t in 0..(T : ℝ), q t

theorem density_zero (ω : SampleSpace)
    (hω : ∀ T : ℝ≥0, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)),
      clockPath ω t.toNNReal ≠ 0) (q : ℝ → ℝ) (hq : supportedAtZero ω q) (T : ℝ≥0) :
    q =ᵐ[(volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))] 0 := by
  filter_upwards [hω T, ae_restrict_mem measurableSet_Ioc] with t ht hpos
  exact hq t hpos.1 ht

theorem mass_zero (ω : SampleSpace)
    (hω : ∀ T : ℝ≥0, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)),
      clockPath ω t.toNNReal ≠ 0) (q : ℝ → ℝ) (hq : supportedAtZero ω q) (T : ℝ≥0) :
    mass q T = 0 := by
  rw [mass, intervalIntegral.integral_of_le T.coe_nonneg]
  exact integral_eq_zero_of_ae (density_zero ω hω q hq T)

theorem no_density_clock : ∀ᵐ ω ∂gaussianProduct, ∀ q : ℝ → ℝ,
    supportedAtZero ω q → ∀ T : ℝ≥0, mass q T = 0 := by
  filter_upwards [zero_time_all] with ω hω
  intro q hq T
  exact mass_zero ω hω q hq T

theorem clock_is_identity : ∀ᵐ ω ∂gaussianProduct, ∀ q : ℝ → ℝ,
    supportedAtZero ω q → ∀ (κ T : ℝ≥0),
      StickyTimeChangeClock.clock κ (fun s => (mass q s).toNNReal) T = T := by
  filter_upwards [no_density_clock] with ω hω
  intro q hq κ T
  simp only [StickyTimeChangeClock.clock, hω q hq T, Real.toNNReal_zero, mul_zero, add_zero]

theorem represented_localMass_zero : ∀ᵐ ω ∂gaussianProduct, ∀ (q : ℝ → ℝ) (L : ℝ≥0 → ℝ≥0),
    supportedAtZero ω q → (∀ T, (L T : ℝ) = mass q T) → L = 0 := by
  filter_upwards [no_density_clock] with ω hω
  intro q L hq hL
  funext T
  apply NNReal.coe_injective
  rw [hL T, hω q hq T]
  rfl

end OperatorDerivativeRewrite.Foundation.BrownianZeroClockObstruction
