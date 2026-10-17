import Foundation.FourierPathControlHessian
import Foundation.FourierPathTimeGradient

/-! A genuine iterated Bochner L-one two-time density for the control Hessian. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathTimeHessian
open HigherHeatDyadicLaws HigherHeatFourierBanach FourierPathBoundedControls
open BochnerTimeControlPairing FourierPathTimeGradient FourierPathControlHessian
open FourierPathControlGradient

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def timeHessian (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) :
    BochnerTimeControlPairing.Field (BochnerTimeControlPairing.Field (TestSpace levels ξ)) :=
  (timeGradient levels ξ m hm S hS).compLpL 1 volume (timeGradient levels ξ m hm T hT q)

theorem timeHessian_bound (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) :
    ‖timeHessian levels ξ m hm S T hS hT q‖ ≤ (1+(S:ℝ)⁻¹)*(1+(T:ℝ)⁻¹)*‖q‖ := by
  have hG : ‖timeGradient levels ξ m hm S hS‖ ≤ 1+(S:ℝ)⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    exact timeGradient_bound levels ξ m hm S hS
  calc
    _ ≤ ‖timeGradient levels ξ m hm S hS‖*‖timeGradient levels ξ m hm T hT q‖ :=
      (timeGradient levels ξ m hm S hS).norm_compLp_le _
    _ ≤ (1+(S:ℝ)⁻¹)*((1+(T:ℝ)⁻¹)*‖q‖) := mul_le_mul hG
      (timeGradient_bound levels ξ m hm T hT q) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem timeHessian_outer_pairing (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control) :
    pairing (BochnerTimeControlPairing.Field (TestSpace levels ξ)) u
      (timeHessian levels ξ m hm S T hS hT q) =
      timeGradient levels ξ m hm S hS (gradient levels ξ m hm T hT q u) := by
  have hh := pairing_compLp ((timeGradient levels ξ m hm S hS).restrictScalars ℝ) u
    (timeGradient levels ξ m hm T hT q)
  change pairing (BochnerTimeControlPairing.Field (TestSpace levels ξ)) u
    (timeHessian levels ξ m hm S T hS hT q) =
    timeGradient levels ξ m hm S hS (pairing (TestSpace levels ξ) u (timeGradient levels ξ m hm T hT q)) at hh
  rwa [timeGradient_pairing] at hh

theorem timeHessian_pairing (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) (u v : Control) :
    pairing (TestSpace levels ξ) v
      (pairing (BochnerTimeControlPairing.Field (TestSpace levels ξ)) u
        (timeHessian levels ξ m hm S T hS hT q)) = hessian levels ξ m hm S T hS hT q u v := by
  rw [timeHessian_outer_pairing, timeGradient_pairing]
  rfl

theorem timeHessian_integral (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ) (u v : Control) :
    (∫ t, u t • (∫ s, v s • timeHessian levels ξ m hm S T hS hT q t s)) =
      hessian levels ξ m hm S T hS hT q u v := by
  let K := timeHessian levels ξ m hm S T hS hT q
  have hi : Integrable (fun t => u t • K t) :=
    memLp_one_iff_integrable.mp ((Lp.memLp u).smul (Lp.memLp K))
  have hh := (pairing (TestSpace levels ξ) v).integral_comp_comm hi
  simp_rw [map_smul] at hh
  rw [← pairing_integral (BochnerTimeControlPairing.Field (TestSpace levels ξ))] at hh
  calc
    _ = ∫ t, u t • pairing (TestSpace levels ξ) v (K t) := by simp_rw [pairing_integral]; rfl
    _ = pairing (TestSpace levels ξ) v
        (pairing (BochnerTimeControlPairing.Field (TestSpace levels ξ)) u K) := hh
    _ = _ := timeHessian_pairing levels ξ m hm S T hS hT q u v

theorem timeHessian_unique (m : ℕ) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (q : TestSpace levels ξ)
    (K : BochnerTimeControlPairing.Field (BochnerTimeControlPairing.Field (TestSpace levels ξ)))
    (hK : ∀ u v : Control, pairing (TestSpace levels ξ) v
      (pairing (BochnerTimeControlPairing.Field (TestSpace levels ξ)) u K) =
        hessian levels ξ m hm S T hS hT q u v) :
    K = timeHessian levels ξ m hm S T hS hT q := by
  apply pairing_injective (BochnerTimeControlPairing.Field (TestSpace levels ξ))
  apply ContinuousLinearMap.ext
  intro u
  apply pairing_injective (TestSpace levels ξ)
  apply ContinuousLinearMap.ext
  intro v
  exact (hK u v).trans (timeHessian_pairing levels ξ m hm S T hS hT q u v).symm

end OperatorDerivativeRewrite.Foundation.FourierPathTimeHessian
