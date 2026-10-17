import Foundation.FourierPathGradientCommutation
import Foundation.FourierPathControlFrechet

/-! A genuine symmetric second Frechet derivative and iterated closed path derivative. -/
noncomputable section
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathControlHessian
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatFourierBanach
open FourierPathBoundedControls FourierPathControlGradient FourierPathControlGradientSeries
open FourierPathControlSymbols FourierPathGradientCommutation
open HigherHeatFourierTranslations HigherHeatFourierPathSemigroup FourierPathDirectionalOperator

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def hessian (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) : Control →L[ℝ] (Control →L[ℝ] TestSpace levels ξ) :=
  ((gradient levels ξ m hm S hS).restrictScalars ℝ).comp (gradient levels ξ m hm T hT q)

theorem hessian_bound (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) :
    ‖hessian levels ξ m hm S T hS hT q‖ ≤ (1+(S:ℝ)⁻¹)*(1+(T:ℝ)⁻¹)*‖q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖gradient levels ξ m hm S hS (gradient levels ξ m hm T hT q u)‖ ≤ _
  calc
    _ ≤ (1+(S:ℝ)⁻¹)*‖gradient levels ξ m hm T hT q u‖ := gradient_bound levels ξ m hm S hS _
    _ ≤ (1+(S:ℝ)⁻¹)*((1+(T:ℝ)⁻¹)*‖q‖*‖u‖) :=
      mul_le_mul_of_nonneg_left (bilinear_bound levels ξ m hm T hT q u) (by positivity)
    _ = _ := by ring

theorem hessian_symmetric (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) (u v : Control) :
    hessian levels ξ m hm S T hS hT q u v = hessian levels ξ m hm S T hS hT q v u := by
  change gradient levels ξ m hm S hS (gradient levels ξ m hm T hT q u) v =
    gradient levels ξ m hm S hS (gradient levels ξ m hm T hT q v) u
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  rw [gradient_mk, gradient_mk, gradient_mk, gradient_mk]
  congr 1
  apply Subtype.ext
  funext i
  rw [family_coordinate, family_coordinate, family_coordinate, family_coordinate,
    symbolMap_apply, symbolMap_apply, symbolMap_apply, symbolMap_apply]
  ring

theorem derivative_hasFDerivAt (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control) :
    HasFDerivAt (fun v => gradient levels ξ m hm (S+T) (add_pos hS hT)
      (translation levels ξ (direction v) q))
      (hessian levels ξ m hm S T hS hT (translation levels ξ (direction u) q)) u := by
  have hh := ((gradient levels ξ m hm S hS).restrictScalars ℝ).hasFDerivAt.comp u
    (FourierPathControlFrechet.orbit_hasFDerivAt levels ξ m hm T hT q u)
  have he : (fun v => gradient levels ξ m hm S hS
      (translation levels ξ (direction v) (evolution levels ξ m hm T q))) =
      (fun v => gradient levels ξ m hm (S+T) (add_pos hS hT) (translation levels ξ (direction v) q)) := by
    funext v
    ext w
    rw [← evolution_translation, heat_split]
  change HasFDerivAt (fun v => gradient levels ξ m hm S hS
    (translation levels ξ (direction v) (evolution levels ξ m hm T q))) _ u at hh
  rwa [he] at hh

theorem second_fderiv (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control) :
    HasFDerivAt (fun v => fderiv ℝ
      (fun w => translation levels ξ (direction w) (evolution levels ξ m hm (S+T) q)) v)
      (hessian levels ξ m hm S T hS hT (translation levels ξ (direction u) q)) u := by
  have he : (fun v => fderiv ℝ
      (fun w => translation levels ξ (direction w) (evolution levels ξ m hm (S+T) q)) v) =
      (fun v => gradient levels ξ m hm (S+T) (add_pos hS hT) (translation levels ξ (direction v) q)) := by
    funext v
    exact (FourierPathControlFrechet.orbit_hasFDerivAt levels ξ m hm (S+T) (add_pos hS hT) q v).fderiv
  rw [he]
  exact derivative_hasFDerivAt levels ξ m hm S T hS hT q u

theorem hessian_graph (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) (u v : Control) :
    (gradient levels ξ m hm (S+T) (add_pos hS hT) q u, hessian levels ξ m hm S T hS hT q u v) ∈
      graph levels ξ (direction v) := by
  have hh := atControl_preserves_graph levels ξ m hm S hS u (direction v) _
    (gradient_graph levels ξ m hm T hT q v)
  change (gradient levels ξ m hm S hS (evolution levels ξ m hm T q) u,
    hessian levels ξ m hm S T hS hT q v u) ∈ graph levels ξ (direction v) at hh
  rw [heat_split, hessian_symmetric levels ξ m hm S T hS hT q v u] at hh
  exact hh

end OperatorDerivativeRewrite.Foundation.FourierPathControlHessian
