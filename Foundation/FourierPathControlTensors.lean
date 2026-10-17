import Foundation.FourierPathSmoothControls
import Foundation.FourierPathTimeGradientRealization

/-! Genuine all-order control derivative tensors and their stochastic expectation realization. -/
noncomputable section
open Filter MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathControlTensors
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathBoundedControls HigherHeatFourierTranslations HigherHeatFourierPathSemigroup
open HigherHeatInterpolatedPaths HigherHeatWeightedPaths FourierPathSmoothControls

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def tensor (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (n : ℕ) (u : Control) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => Control) (TestSpace levels ξ) :=
  iteratedFDeriv ℝ n (fun v => translation levels ξ (direction v) (evolution levels ξ m hm T q)) u

theorem scalar_tensor (L : TestSpace levels ξ →L[ℂ] ℂ)
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ)
    (n : ℕ) (u : Control) (controls : Fin n → Control) :
    iteratedFDeriv ℝ n
      (fun v => L (translation levels ξ (direction v) (evolution levels ξ m hm T q))) u controls =
      L (tensor levels ξ m hm T hT q n u controls) := by
  have hh := (L.restrictScalars ℝ).iteratedFDeriv_comp_left (x := u)
    (orbit_contDiff_nat levels ξ m hm n T hT q).contDiffAt (i := n) le_rfl
  have he := DFunLike.congr_fun hh controls
  exact he

theorem realized_tensor (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (n : ℕ) (u : Control) (controls : Fin n → Control) (path : Path) :
    iteratedFDeriv ℝ n
      (fun v => realize levels ξ (evolution levels ξ m hm T q) (addPath (direction v) path)) u controls =
      realize levels ξ (tensor levels ξ m hm T hT q n u controls) path := by
  let L : TestSpace levels ξ →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ path).comp (realize levels ξ)
  have hh := scalar_tensor levels ξ L m hm T hT q n u controls
  have he : (fun v => L (translation levels ξ (direction v) (evolution levels ξ m hm T q))) =
      (fun v => realize levels ξ (evolution levels ξ m hm T q) (addPath (direction v) path)) := by
    funext v
    exact realize_translation levels ξ (direction v) (evolution levels ξ m hm T q) path
  rw [he] at hh
  exact hh

theorem weighted_tensor_limit (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ)
    (n : ℕ) (u : Control) (controls : Fin n → Control) :
    Tendsto (fun j => ∫ path, pathWeight k hk H hH j path •
      realize levels ξ (tensor levels ξ m hm T hT q n u controls) path ∂probabilityPath k hk H hH j)
      atTop (𝓝 (iteratedFDeriv ℝ n
        (fun v => expectation levels ξ k hk H hH
          (translation levels ξ (direction v) (evolution levels ξ m hm T q))) u controls)) := by
  rw [scalar_tensor levels ξ (expectation levels ξ k hk H hH) m hm T hT q n u controls]
  exact weighted_expectation_limit levels ξ k hk H hH _

theorem signed_tensor_limit (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ)
    (n : ℕ) (u : Control) (controls : Fin n → Control) :
    Tendsto (fun j => ∫ᵛ path, realize levels ξ (tensor levels ξ m hm T hT q n u controls) path
      ∂<•signedPath k hk H hH j) atTop (𝓝 (iteratedFDeriv ℝ n
        (fun v => expectation levels ξ k hk H hH
          (translation levels ξ (direction v) (evolution levels ξ m hm T q))) u controls)) := by
  rw [scalar_tensor levels ξ (expectation levels ξ k hk H hH) m hm T hT q n u controls]
  exact expectation_limit levels ξ k hk H hH _

theorem weighted_derivative_realization (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ)
    (n : ℕ) (u : Control) (controls : Fin n → Control) :
    (∀ j, Integrable (fun path => pathWeight k hk H hH j path •
      iteratedFDeriv ℝ n (fun v => realize levels ξ (evolution levels ξ m hm T q)
        (addPath (direction v) path)) u controls) (probabilityPath k hk H hH j)) ∧
    Tendsto (fun j => ∫ path, pathWeight k hk H hH j path •
      iteratedFDeriv ℝ n (fun v => realize levels ξ (evolution levels ξ m hm T q)
        (addPath (direction v) path)) u controls ∂probabilityPath k hk H hH j) atTop
      (𝓝 (iteratedFDeriv ℝ n (fun v => expectation levels ξ k hk H hH
        (translation levels ξ (direction v) (evolution levels ξ m hm T q))) u controls)) := by
  simp_rw [realized_tensor levels ξ m hm T hT q n u controls]
  exact ⟨fun j => weighted_test_integrable levels ξ k hk H hH j _,
    weighted_tensor_limit levels ξ m k hm hk T H hT hH q n u controls⟩

end OperatorDerivativeRewrite.Foundation.FourierPathControlTensors
