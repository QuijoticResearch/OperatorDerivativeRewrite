import Foundation.FourierPathControlFrechetSeries

/-! Genuine infinite-dimensional Frechet control calculus for realized higher-heat path tests. -/
noncomputable section
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathControlFrechet
open FourierPathBoundedControls FourierPathControlSymbols HigherHeatDyadicLaws
open HigherHeatContinuousCylinders HigherHeatFourierBanach HigherHeatFourierTranslations
open HigherHeatFourierPathSemigroup FourierPathControlGradient

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem orbit_hasFDerivAt (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control) :
    HasFDerivAt (fun v => translation levels ξ (direction v) (evolution levels ξ m hm T q))
      (gradient levels ξ m hm T hT (translation levels ξ (direction u) q)) u := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  have hh := ((kernel levels ξ).mkQL.restrictScalars ℝ).hasFDerivAt.comp u
    (FourierPathControlFrechetSeries.coefficient_orbit_hasFDerivAt levels ξ a m hm T hT u)
  convert hh using 1
  · funext v
    rw [evolution_mk, translation_mk]
    rfl
  · ext v
    rw [translation_mk, gradient_mk]
    rfl

theorem direction_zero : direction (0:Control) = zeroPath := by
  apply Subtype.ext
  ext t
  change atTime t 0 = 0
  exact map_zero (atTime t)

theorem orbit_hasFDerivAt_zero (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) :
    HasFDerivAt (fun v => translation levels ξ (direction v) (evolution levels ξ m hm T q))
      (gradient levels ξ m hm T hT q) 0 := by
  have hh := orbit_hasFDerivAt levels ξ m hm T hT q 0
  rwa [direction_zero, translation_zero] at hh

theorem realized_hasFDerivAt (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (ω : Path) (u : Control) :
    HasFDerivAt (fun v => realize levels ξ (evolution levels ξ m hm T q) (addPath (direction v) ω))
      ((((BoundedContinuousFunction.evalCLM ℂ ω).comp (realize levels ξ)).restrictScalars ℝ).comp
        (gradient levels ξ m hm T hT (translation levels ξ (direction u) q))) u := by
  let L : TestSpace levels ξ →L[ℝ] ℂ :=
    ((BoundedContinuousFunction.evalCLM ℂ ω).comp (realize levels ξ)).restrictScalars ℝ
  have hh := L.hasFDerivAt.comp u (orbit_hasFDerivAt levels ξ m hm T hT q u)
  convert hh using 1
  funext v
  exact (realize_translation levels ξ (direction v) (evolution levels ξ m hm T q) ω).symm

theorem expectation_hasFDerivAt (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ) (u : Control) :
    HasFDerivAt (fun v => expectation levels ξ k hk H hH
      (translation levels ξ (direction v) (evolution levels ξ m hm T q)))
      (((expectation levels ξ k hk H hH).restrictScalars ℝ).comp
        (gradient levels ξ m hm T hT (translation levels ξ (direction u) q))) u := by
  exact ((expectation levels ξ k hk H hH).restrictScalars ℝ).hasFDerivAt.comp u
    (orbit_hasFDerivAt levels ξ m hm T hT q u)

end OperatorDerivativeRewrite.Foundation.FourierPathControlFrechet
