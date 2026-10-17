import Foundation.FourierPathTimeHessian
import Foundation.FourierPathTimeGradientRealization

/-! Genuine scalar two-time Hessian densities and stochastic expectation limits. -/
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathHessianRealization
open HigherHeatDyadicLaws HigherHeatFourierBanach FourierPathBoundedControls
open BochnerTimeControlPairing FourierPathTimeGradient FourierPathControlHessian FourierPathTimeHessian
open HigherHeatInterpolatedPaths HigherHeatWeightedPaths

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def scalarField (L : TestSpace levels ξ →L[ℂ] ℂ)
    (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T) (q : TestSpace levels ξ) :
    BochnerTimeControlPairing.Field (BochnerTimeControlPairing.Field ℂ) :=
  (L.compLpL 1 volume).compLpL 1 volume (timeHessian levels ξ m hm S T hS hT q)

theorem scalarField_bound (L : TestSpace levels ξ →L[ℂ] ℂ)
    (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T) (q : TestSpace levels ξ) :
    ‖scalarField levels ξ L m hm S T hS hT q‖ ≤
      ‖L‖*((1+(S:ℝ)⁻¹)*(1+(T:ℝ)⁻¹)*‖q‖) := by
  calc
    _ ≤ ‖L.compLpL 1 volume‖*‖timeHessian levels ξ m hm S T hS hT q‖ :=
      (L.compLpL 1 volume).norm_compLp_le _
    _ ≤ ‖L‖*((1+(S:ℝ)⁻¹)*(1+(T:ℝ)⁻¹)*‖q‖) :=
      mul_le_mul (ContinuousLinearMap.norm_compLpL_le L)
        (timeHessian_bound levels ξ m hm S T hS hT q) (norm_nonneg _) (norm_nonneg L)

theorem scalarField_pairing (L : TestSpace levels ξ →L[ℂ] ℂ)
    (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) (u v : Control) :
    pairing ℂ v (pairing (BochnerTimeControlPairing.Field ℂ) u
      (scalarField levels ξ L m hm S T hS hT q)) = L (hessian levels ξ m hm S T hS hT q u v) := by
  have ho := pairing_compLp ((L.compLpL 1 volume).restrictScalars ℝ) u
    (timeHessian levels ξ m hm S T hS hT q)
  change pairing (BochnerTimeControlPairing.Field ℂ) u (scalarField levels ξ L m hm S T hS hT q) =
    L.compLpL 1 volume (pairing (BochnerTimeControlPairing.Field (TestSpace levels ξ)) u
      (timeHessian levels ξ m hm S T hS hT q)) at ho
  rw [ho]
  have hi := pairing_compLp (L.restrictScalars ℝ) v
    (pairing (BochnerTimeControlPairing.Field (TestSpace levels ξ)) u (timeHessian levels ξ m hm S T hS hT q))
  change pairing ℂ v (L.compLpL 1 volume
    (pairing (BochnerTimeControlPairing.Field (TestSpace levels ξ)) u (timeHessian levels ξ m hm S T hS hT q))) =
    L (pairing (TestSpace levels ξ) v
      (pairing (BochnerTimeControlPairing.Field (TestSpace levels ξ)) u (timeHessian levels ξ m hm S T hS hT q))) at hi
  rw [hi, timeHessian_pairing]

theorem nested_integral_pairing (K : BochnerTimeControlPairing.Field (BochnerTimeControlPairing.Field ℂ))
    (u v : Control) :
    (∫ t, u t • (∫ s, v s • K t s)) = pairing ℂ v (pairing (BochnerTimeControlPairing.Field ℂ) u K) := by
  have hi : Integrable (fun t => u t • K t) :=
    memLp_one_iff_integrable.mp ((Lp.memLp u).smul (Lp.memLp K))
  have hh := (pairing ℂ v).integral_comp_comm hi
  simp_rw [map_smul] at hh
  rw [← pairing_integral (BochnerTimeControlPairing.Field ℂ)] at hh
  calc
    _ = ∫ t, u t • pairing ℂ v (K t) := by simp_rw [pairing_integral]
    _ = _ := hh

theorem scalarField_integral (L : TestSpace levels ξ →L[ℂ] ℂ)
    (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) (u v : Control) :
    (∫ t, u t • (∫ s, v s • scalarField levels ξ L m hm S T hS hT q t s)) =
      L (hessian levels ξ m hm S T hS hT q u v) := by
  rw [nested_integral_pairing]
  exact scalarField_pairing levels ξ L m hm S T hS hT q u v

theorem realized_hessian_integral (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) (ω : HigherHeatContinuousCylinders.Path) (u v : Control) :
    (∫ t, u t • (∫ s, v s • scalarField levels ξ
      (FourierPathTimeGradientRealization.evaluation levels ξ ω) m hm S T hS hT q t s)) =
      realize levels ξ (hessian levels ξ m hm S T hS hT q u v) ω :=
  scalarField_integral levels ξ _ m hm S T hS hT q u v

theorem weighted_hessian_limit (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (S T H : ℝ≥0) (hS : 0 < S) (hT : 0 < T) (hH : 0 < H)
    (q : TestSpace levels ξ) (u v : Control) :
    Tendsto (fun n => ∫ ω, pathWeight k hk H hH n ω •
      realize levels ξ (hessian levels ξ m hm S T hS hT q u v) ω ∂probabilityPath k hk H hH n)
      atTop (𝓝 (∫ t, u t • (∫ s, v s • scalarField levels ξ
        (expectation levels ξ k hk H hH) m hm S T hS hT q t s))) := by
  rw [scalarField_integral]
  exact weighted_expectation_limit levels ξ k hk H hH _

end OperatorDerivativeRewrite.Foundation.FourierPathHessianRealization
