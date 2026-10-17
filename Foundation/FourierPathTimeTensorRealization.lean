import Foundation.FourierPathTimeTensorIdentity
import Foundation.FourierPathControlTensors

/-! Actual all-order scalar time fields, native derivative realization and stochastic laws. -/
noncomputable section
open Filter MeasureTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathTimeTensorRealization
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathBoundedControls BochnerControlTowers FourierPathTimeTowers FourierPathTimeTensorIdentity
open HigherHeatFourierTranslations HigherHeatFourierPathSemigroup HigherHeatInterpolatedPaths HigherHeatWeightedPaths

def mapTower (B C : Space) (L : B →L[ℝ] C) : (n : ℕ) → (tower B n →L[ℝ] tower C n)
  | 0 => L
  | n+1 => lift (tower B n) (tower C n) (mapTower B C L n)

theorem mapTower_norm (B C : Space) (L : B →L[ℝ] C) (n : ℕ) : ‖mapTower B C L n‖ ≤ ‖L‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (lift_norm _ _ _).trans ih

theorem mapTower_evaluate (B C : Space) (L : B →L[ℝ] C) (n : ℕ)
    (controls : Fin n → Control) (K : tower B n) :
    evaluate C n controls (mapTower B C L n K) = L (evaluate B n controls K) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := pairing_lift (tower B n) (tower C n) (mapTower B C L n) (controls 0) K
    have he := congrArg (evaluate C n (fun j => controls j.succ)) hp
    exact he.trans (ih _ _)

abbrev scalarBase : Space := BochnerControlTowers.of ℂ

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem vector_density_unique (m : ℕ) (hm : 0 < m) (H : ℝ≥0) (hH : 0 < H)
    (n : ℕ) (hn : 0 < n) (q : TestSpace levels ξ) (K : tower (base levels ξ) n)
    (hK : ∀ controls, evaluate (base levels ξ) n controls K =
      iteratedFDeriv ℝ n (fun v => translation levels ξ (direction v)
        (evolution levels ξ m hm H q)) 0 controls) :
    K = normalizedDensity levels ξ m hm H hH n hn q := by
  apply evaluate_separates (base levels ξ) n
  intro controls
  exact (hK controls).trans (normalized_pairing levels ξ m hm H hH n hn controls q).symm

def scalarDensity (L : TestSpace levels ξ →L[ℝ] ℂ)
    (m : ℕ) (hm : 0 < m) (H : ℝ≥0) (hH : 0 < H)
    (n : ℕ) (hn : 0 < n) (q : TestSpace levels ξ) : tower scalarBase n :=
  mapTower (base levels ξ) scalarBase L n (normalizedDensity levels ξ m hm H hH n hn q)

theorem scalar_pairing (L : TestSpace levels ξ →L[ℝ] ℂ)
    (m : ℕ) (hm : 0 < m) (H : ℝ≥0) (hH : 0 < H)
    (n : ℕ) (hn : 0 < n) (q : TestSpace levels ξ) (controls : Fin n → Control) :
    evaluate scalarBase n controls (scalarDensity levels ξ L m hm H hH n hn q) =
      L (iteratedFDeriv ℝ n (fun v => translation levels ξ (direction v)
        (evolution levels ξ m hm H q)) 0 controls) := by
  rw [scalarDensity, mapTower_evaluate, normalized_pairing]

theorem scalar_bound (L : TestSpace levels ξ →L[ℝ] ℂ)
    (m : ℕ) (hm : 0 < m) (H : ℝ≥0) (hH : 0 < H)
    (n : ℕ) (hn : 0 < n) (q : TestSpace levels ξ) :
    ‖scalarDensity levels ξ L m hm H hH n hn q‖ ≤
      ‖L‖*((1+((H/(n:ℝ≥0)):ℝ)⁻¹)^n*‖q‖) := by
  have hk : ‖normalizedDensity levels ξ m hm H hH n hn q‖ ≤
      (1+((H/(n:ℝ≥0)):ℝ)⁻¹)^n*‖q‖ :=
    (density levels ξ m hm (H/(n:ℝ≥0)) (div_pos hH (by exact_mod_cast hn)) n).le_of_opNorm_le
      (density_norm levels ξ m hm _ _ n) q
  calc
    _ ≤ ‖mapTower (base levels ξ) scalarBase L n‖*‖normalizedDensity levels ξ m hm H hH n hn q‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul (mapTower_norm _ _ _ _) hk (norm_nonneg _) (norm_nonneg L)

theorem realized_pairing (m : ℕ) (hm : 0 < m) (H : ℝ≥0) (hH : 0 < H)
    (n : ℕ) (hn : 0 < n) (q : TestSpace levels ξ) (controls : Fin n → Control) (path : Path) :
    evaluate scalarBase n controls (scalarDensity levels ξ
      ((FourierPathTimeGradientRealization.evaluation levels ξ path).restrictScalars ℝ) m hm H hH n hn q) =
      iteratedFDeriv ℝ n (fun v => realize levels ξ (evolution levels ξ m hm H q)
        (addPath (direction v) path)) 0 controls := by
  rw [scalar_pairing]
  exact (FourierPathControlTensors.realized_tensor levels ξ m hm H hH q n 0 controls path).symm

theorem expected_pairing (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (H K : ℝ≥0) (hH : 0 < H) (hK : 0 < K) (n : ℕ) (hn : 0 < n)
    (q : TestSpace levels ξ) (controls : Fin n → Control) :
    evaluate scalarBase n controls (scalarDensity levels ξ
      ((expectation levels ξ k hk K hK).restrictScalars ℝ) m hm H hH n hn q) =
      iteratedFDeriv ℝ n (fun v => expectation levels ξ k hk K hK
        (translation levels ξ (direction v) (evolution levels ξ m hm H q))) 0 controls := by
  rw [scalar_pairing]
  exact (FourierPathControlTensors.scalar_tensor levels ξ (expectation levels ξ k hk K hK)
    m hm H hH q n 0 controls).symm

theorem weighted_density_realization (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (H K : ℝ≥0) (hH : 0 < H) (hK : 0 < K) (n : ℕ) (hn : 0 < n)
    (q : TestSpace levels ξ) (controls : Fin n → Control) :
    (∀ j, Integrable (fun path => pathWeight k hk K hK j path •
      iteratedFDeriv ℝ n (fun v => realize levels ξ (evolution levels ξ m hm H q)
        (addPath (direction v) path)) 0 controls) (probabilityPath k hk K hK j)) ∧
    Tendsto (fun j => ∫ path, pathWeight k hk K hK j path •
      iteratedFDeriv ℝ n (fun v => realize levels ξ (evolution levels ξ m hm H q)
        (addPath (direction v) path)) 0 controls ∂probabilityPath k hk K hK j) atTop
      (𝓝 (evaluate scalarBase n controls (scalarDensity levels ξ
        ((expectation levels ξ k hk K hK).restrictScalars ℝ) m hm H hH n hn q))) := by
  rw [expected_pairing]
  exact FourierPathControlTensors.weighted_derivative_realization levels ξ m k hm hk H K hH hK q n 0 controls

end OperatorDerivativeRewrite.Foundation.FourierPathTimeTensorRealization
