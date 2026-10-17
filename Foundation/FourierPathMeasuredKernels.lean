import Foundation.FourierPathKernelFunctionals

/-! Measurable realization of complete path tests against arbitrary integrable densities. -/
noncomputable section
open MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathMeasuredKernels
open HigherHeatContinuousCylinders HigherHeatFourierBanach FourierPathKernelFunctionals

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (levels : ℕ → ℕ) (ξ : (i : ℕ) → HigherHeatDyadicLaws.Grid (levels i))
  (w : α → ℂ) (hw : Integrable w μ) (Φ : α → Path) (hΦ : Measurable Φ)

include hw hΦ in
theorem integrable (q : TestSpace levels ξ) :
    Integrable (fun y => w y * realize levels ξ q (Φ y)) μ :=
  hw.mul_bdd ((realize levels ξ q).continuous.measurable.comp hΦ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => test_bound levels ξ q (Φ y))

include hw hΦ in
theorem bound (q : TestSpace levels ξ) :
    ‖∫ y, w y * realize levels ξ q (Φ y) ∂μ‖ ≤ (∫ y, ‖w y‖ ∂μ) * ‖q‖ := by
  calc
    _ ≤ ∫ y, ‖w y * realize levels ξ q (Φ y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖w y‖ * ‖q‖ ∂μ := by
      apply integral_mono (integrable μ levels ξ w hw Φ hΦ q).norm (hw.norm.mul_const ‖q‖)
      intro y
      calc
        _ = ‖w y‖ * ‖realize levels ξ q (Φ y)‖ := norm_mul _ _
        _ ≤ ‖w y‖ * ‖q‖ :=
          mul_le_mul_of_nonneg_left (test_bound levels ξ q (Φ y)) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

def functional : TestSpace levels ξ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun q := ∫ y, w y * realize levels ξ q (Φ y) ∂μ
      map_add' := by
        intro q r
        simp only [map_add, BoundedContinuousFunction.add_apply, mul_add]
        exact integral_add (integrable μ levels ξ w hw Φ hΦ q)
          (integrable μ levels ξ w hw Φ hΦ r)
      map_smul' := by
        intro c q
        simp only [map_smul, BoundedContinuousFunction.smul_apply, smul_eq_mul]
        simp_rw [mul_left_comm (w _) c]
        exact integral_const_mul _ _ }
    (∫ y, ‖w y‖ ∂μ) (bound μ levels ξ w hw Φ hΦ)

theorem functional_apply (q : TestSpace levels ξ) :
    functional μ levels ξ w hw Φ hΦ q = ∫ y, w y * realize levels ξ q (Φ y) ∂μ := rfl

theorem functional_norm : ‖functional μ levels ξ w hw Φ hΦ‖ ≤ ∫ y, ‖w y‖ ∂μ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _)
  exact bound μ levels ξ w hw Φ hΦ

end OperatorDerivativeRewrite.Foundation.FourierPathMeasuredKernels
