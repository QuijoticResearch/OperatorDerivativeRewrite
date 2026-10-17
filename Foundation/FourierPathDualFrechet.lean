import Foundation.FourierPathDualFrechetSeries

/-! Frechet differentiation of actual heat-smoothed path translations in the dual control space. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualFrechet
open FourierPathDualControls HigherHeatDyadicLaws HigherHeatContinuousCylinders
open HigherHeatFourierBanach HigherHeatFourierTranslations HigherHeatFourierPathSemigroup
open FourierPathDualGradient

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem orbit_hasFDerivAt (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control m) :
    HasFDerivAt (fun v => translation levels ξ (direction m v) (evolution levels ξ m h.out T q))
      (gradient levels ξ m T hT (translation levels ξ (direction m u) q)) u := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  have hh := ((kernel levels ξ).mkQL.restrictScalars ℝ).hasFDerivAt.comp u
    (FourierPathDualFrechetSeries.coefficient_orbit_hasFDerivAt m levels ξ a T hT u)
  convert hh using 1
  · funext v
    rw [evolution_mk, translation_mk]
    rfl
  · ext v
    rw [translation_mk, gradient_mk]
    rfl

theorem direction_zero (m : ℕ) [Fact (0 < m)] : direction m (0 : Control m) = zeroPath := by
  apply Subtype.ext
  ext t
  change (∫ s in (0 : ℝ)..t, (0 : Control m) s) = 0
  have hz : ⇑(0 : Control m) =ᵐ[volume] (fun _ : ℝ => 0) :=
    Lp.coeFn_zero ℝ (exponent m) volume
  rw [intervalIntegral.integral_congr_ae (hz.mono (fun s hs _ => hs))]
  simp

theorem orbit_hasFDerivAt_zero (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) :
    HasFDerivAt (fun v => translation levels ξ (direction m v) (evolution levels ξ m h.out T q))
      (gradient levels ξ m T hT q) 0 := by
  have hh := orbit_hasFDerivAt levels ξ m T hT q 0
  rwa [direction_zero, translation_zero] at hh

theorem realized_hasFDerivAt (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (ω : Path) (u : Control m) :
    HasFDerivAt (fun v => realize levels ξ (evolution levels ξ m h.out T q)
      (addPath (direction m v) ω))
      ((((BoundedContinuousFunction.evalCLM ℂ ω).comp (realize levels ξ)).restrictScalars ℝ).comp
        (gradient levels ξ m T hT (translation levels ξ (direction m u) q))) u := by
  let L : TestSpace levels ξ →L[ℝ] ℂ :=
    ((BoundedContinuousFunction.evalCLM ℂ ω).comp (realize levels ξ)).restrictScalars ℝ
  have hh := L.hasFDerivAt.comp u (orbit_hasFDerivAt levels ξ m T hT q u)
  convert hh using 1
  funext v
  exact (realize_translation levels ξ (direction m v) (evolution levels ξ m h.out T q) ω).symm

theorem expectation_hasFDerivAt (m : ℕ) [h : Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ) (u : Control m) :
    HasFDerivAt (fun v => expectation levels ξ k hk H hH
      (translation levels ξ (direction m v) (evolution levels ξ m h.out T q)))
      (((expectation levels ξ k hk H hH).restrictScalars ℝ).comp
        (gradient levels ξ m T hT (translation levels ξ (direction m u) q))) u :=
  ((expectation levels ξ k hk H hH).restrictScalars ℝ).hasFDerivAt.comp u
    (orbit_hasFDerivAt levels ξ m T hT q u)

end OperatorDerivativeRewrite.Foundation.FourierPathDualFrechet
