import Foundation.FourierPathGradientCommutation
import Foundation.FourierPathControlFrechet
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Genuine smoothness of all orders under bounded time-control perturbations. -/
noncomputable section
open scoped NNReal Topology BoundedContinuousFunction ContDiff
namespace OperatorDerivativeRewrite.Foundation.FourierPathSmoothControls
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathBoundedControls FourierPathControlGradient FourierPathGradientCommutation
open HigherHeatFourierTranslations HigherHeatFourierPathSemigroup

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem orbit_contDiff_nat (m : ℕ) (hm : 0 < m) (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) :
    ContDiff ℝ n (fun u => translation levels ξ (direction u) (evolution levels ξ m hm T q)) := by
  induction n generalizing T q with
  | zero =>
    apply contDiff_zero.mpr
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (FourierPathControlFrechet.orbit_hasFDerivAt levels ξ m hm T hT q u).continuousAt
  | succ n ih =>
    let R : ℝ≥0 := T/2
    have hR : 0 < R := div_pos hT (by norm_num)
    have he : R+R=T := by dsimp [R]; ring
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun u => gradient levels ξ m hm T hT (translation levels ξ (direction u) q), ?_, ?_⟩
    · have hg := ((gradient levels ξ m hm R hR).restrictScalars ℝ).contDiff.comp (ih R hR q)
      have hf : (fun u => gradient levels ξ m hm R hR
          (translation levels ξ (direction u) (evolution levels ξ m hm R q))) =
          (fun u => gradient levels ξ m hm T hT (translation levels ξ (direction u) q)) := by
        funext u
        ext v
        rw [← evolution_translation]
        simpa only [he] using heat_split levels ξ m hm R hR R
          (translation levels ξ (direction u) q) v
      change ContDiff ℝ n (fun u => gradient levels ξ m hm R hR
        (translation levels ξ (direction u) (evolution levels ξ m hm R q))) at hg
      rwa [hf] at hg
    · intro u
      exact FourierPathControlFrechet.orbit_hasFDerivAt levels ξ m hm T hT q u

theorem orbit_contDiff (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    ContDiff ℝ ∞ (fun u => translation levels ξ (direction u) (evolution levels ξ m hm T q)) :=
  contDiff_infty.mpr (fun n => orbit_contDiff_nat levels ξ m hm n T hT q)

theorem realized_contDiff (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (path : Path) :
    ContDiff ℝ ∞ (fun u => realize levels ξ (evolution levels ξ m hm T q) (addPath (direction u) path)) := by
  let L : TestSpace levels ξ →L[ℝ] ℂ :=
    ((BoundedContinuousFunction.evalCLM ℂ path).comp (realize levels ξ)).restrictScalars ℝ
  have hh := L.contDiff.comp (orbit_contDiff levels ξ m hm T hT q)
  convert hh using 1
  funext u
  exact (realize_translation levels ξ (direction u) (evolution levels ξ m hm T q) path).symm

theorem expectation_contDiff (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ) :
    ContDiff ℝ ∞ (fun u => expectation levels ξ k hk H hH
      (translation levels ξ (direction u) (evolution levels ξ m hm T q))) :=
  ((expectation levels ξ k hk H hH).restrictScalars ℝ).contDiff.comp
    (orbit_contDiff levels ξ m hm T hT q)

end OperatorDerivativeRewrite.Foundation.FourierPathSmoothControls
