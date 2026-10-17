import Foundation.FourierPathControlGradient

/-! Actual bounded gradient operators, heat splitting and mixed derivative commutation. -/
noncomputable section
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathGradientCommutation
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathBoundedControls FourierPathControlGradient FourierPathControlGradientSeries
open FourierPathControlSymbols HigherHeatFourierTranslations HigherHeatFourierPathSemigroup
open FourierPathDirectionalOperator

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def atControl (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u : Control) :
    TestSpace levels ξ →L[ℂ] TestSpace levels ξ :=
  LinearMap.mkContinuous
    { toFun := fun q => gradient levels ξ m hm T hT q u
      map_add' := by intro q r; simp
      map_smul' := by intro c q; simp }
    ((1+(T:ℝ)⁻¹)*‖u‖) (fun q => by
      exact (bilinear_bound levels ξ m hm T hT q u).trans_eq (by ring))

theorem atControl_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u : Control) :
    ‖atControl levels ξ m hm T hT u‖ ≤ (1+(T:ℝ)⁻¹)*‖u‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

theorem atControl_mk (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u : Control) (a : Coeff) :
    atControl levels ξ m hm T hT u ((kernel levels ξ).mkQ a) =
      (kernel levels ξ).mkQ (family levels ξ m hm T hT a u) := rfl

theorem gradient_translation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (h : Path) (u : Control) :
    gradient levels ξ m hm T hT (translation levels ξ h q) u =
      translation levels ξ h (gradient levels ξ m hm T hT q u) := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  rw [translation_mk, gradient_mk, gradient_mk, translation_mk]
  congr 1
  apply Subtype.ext
  funext i
  rw [family_coordinate]
  change (a i*characterTest levels ξ i h)*symbolMap levels ξ m T i u =
    (family levels ξ m hm T hT a u i)*characterTest levels ξ i h
  rw [family_coordinate]
  ring

theorem heat_split (m : ℕ) (hm : 0 < m) (S : ℝ≥0) (hS : 0 < S) (T : ℝ≥0)
    (q : TestSpace levels ξ) (u : Control) :
    gradient levels ξ m hm S hS (evolution levels ξ m hm T q) u =
      gradient levels ξ m hm (S+T) (add_pos_of_pos_of_nonneg hS T.coe_nonneg) q u := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  rw [evolution_mk, gradient_mk, gradient_mk]
  congr 1
  apply Subtype.ext
  funext i
  rw [family_coordinate, family_coordinate, coefficientEvolution_apply,
    symbolMap_apply, symbolMap_apply, multiplier_add]
  ring

theorem mixed_commute (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T) (q : TestSpace levels ξ) (u v : Control) :
    gradient levels ξ m hm S hS (gradient levels ξ k hk T hT q v) u =
      gradient levels ξ k hk T hT (gradient levels ξ m hm S hS q u) v := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  rw [gradient_mk, gradient_mk, gradient_mk, gradient_mk]
  congr 1
  apply Subtype.ext
  funext i
  rw [family_coordinate, family_coordinate, family_coordinate, family_coordinate]
  ring

theorem atControl_preserves_graph (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (u : Control) (h : Path) (z : TestSpace levels ξ × TestSpace levels ξ)
    (hz : z ∈ graph levels ξ h) :
    (atControl levels ξ m hm T hT u z.1, atControl levels ξ m hm T hT u z.2) ∈ graph levels ξ h := by
  apply FourierPathDifferentialCommutation.graph_map_of_commutes levels ξ h
    (atControl levels ξ m hm T hT u) ?_ z hz
  intro t q
  exact (gradient_translation levels ξ m hm T hT q (scalePath t h) u).symm

end OperatorDerivativeRewrite.Foundation.FourierPathGradientCommutation
