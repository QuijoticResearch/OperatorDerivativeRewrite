import Foundation.GaussianConditionalIto
import Foundation.GaussianParameterizedIntegral

/-! Future Ito integrals cannot hide in a past-measurable representer.
This is the cancellation step, not an assertion that every volatility
possesses the required sensitivity kernel or observable graph core. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianFutureRigidity
open InfiniteGaussian GaussianPredictableFull GaussianPredictableCutoff GaussianConditionalIto

theorem future_integral_past_zero (S : ℝ≥0) (u : fullPredictable)
    (hu : predictableCut S u = 0) (hp : itoIntegral u ∈ pastL2 S) : u = 0 := by
  have he : pastProjection S (itoIntegral u) = itoIntegral u :=
    (Submodule.starProjection_eq_self_iff).mpr hp
  rw [pastProjection_integral, hu, map_zero] at he
  exact itoIntegral.injective (he.symm.trans (map_zero itoIntegral).symm)

theorem future_integral_eq_past_iff (S : ℝ≥0) (u : fullPredictable)
    (hu : predictableCut S u = 0) (F : GaussianL2) (hF : F ∈ pastL2 S) :
    itoIntegral u = F ↔ u = 0 ∧ F = 0 := by
  constructor
  · intro he
    have hz := future_integral_past_zero S u hu (he ▸ hF)
    exact ⟨hz, by rw [← he, hz, map_zero]⟩
  · rintro ⟨rfl, rfl⟩
    exact map_zero _

/-- Nonzero past volatility suffices; positivity is not needed for this step. -/
theorem deterministic_factor_zero (S : ℝ≥0) (u : fullPredictable)
    (hu : predictableCut S u = 0) (σ : GaussianL2)
    (hσ : σ ∈ pastL2 S) (hne : σ ≠ 0) (c : ℝ)
    (he : itoIntegral u = c • σ) : c = 0 ∧ u = 0 := by
  obtain ⟨hu0, hc⟩ := (future_integral_eq_past_iff S u hu (c • σ)
    ((pastL2 S).smul_mem c hσ)).mp he
  exact ⟨(smul_eq_zero.mp hc).resolve_right hne, hu0⟩

/-- A genuine Bochner-L² family of future integrands admits no nonzero
correction equal to a deterministic multiple of nonzero past coefficients. -/
theorem parameter_deterministic_representer {S : Type*} [MeasurableSpace S]
    (ν : Measure S) (τ : S → ℝ≥0) (u : Lp fullPredictable 2 ν)
    (σ : Lp GaussianL2 2 ν) (κ : S → ℝ)
    (hu : ∀ᵐ s ∂ν, predictableCut (τ s) (u s) = 0)
    (hσ : ∀ᵐ s ∂ν, σ s ∈ pastL2 (τ s))
    (hne : ∀ᵐ s ∂ν, σ s ≠ 0)
    (he : ∀ᵐ s ∂ν, itoIntegral (u s) = (κ s - 1) • σ s) :
    u = 0 ∧ κ =ᵐ[ν] fun _ => 1 := by
  have h : ∀ᵐ s ∂ν, κ s = 1 ∧ u s = 0 := by
    filter_upwards [hu, hσ, hne, he] with s hu hσ hn he
    obtain ⟨hc, hz⟩ := deterministic_factor_zero (τ s) (u s) hu (σ s) hσ hn _ he
    exact ⟨sub_eq_zero.mp hc, hz⟩
  refine ⟨?_, h.mono fun s hs => hs.1⟩
  apply Lp.ext
  filter_upwards [h, Lp.coeFn_zero (E := fullPredictable) (p := 2) (μ := ν)] with s hs hz
  exact hs.2.trans hz.symm

end OperatorDerivativeRewrite.Foundation.GaussianFutureRigidity
