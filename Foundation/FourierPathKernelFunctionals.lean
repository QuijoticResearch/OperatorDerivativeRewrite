import Foundation.FourierPathFutureIntegral

/-! Actual integrable-kernel functionals on completed Fourier path tests. -/
noncomputable section
open MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathKernelFunctionals
open HigherHeatContinuousCylinders HigherHeatFourierBanach

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → HigherHeatDyadicLaws.Grid (levels i))
  (w : ℝ → ℂ) (hw : Integrable w) (Φ : ℝ → Path) (hΦ : Continuous Φ)

theorem test_bound (q : TestSpace levels ξ) (path : Path) :
    ‖realize levels ξ q path‖ ≤ ‖q‖ :=
  ((realize levels ξ q).norm_coe_le_norm path).trans (realize_bound levels ξ q)

include hw hΦ in
theorem kernel_integrable (q : TestSpace levels ξ) :
    Integrable (fun y => w y * realize levels ξ q (Φ y)) :=
  hw.mul_bdd ((realize levels ξ q).continuous.comp hΦ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => test_bound levels ξ q (Φ y))

include hw hΦ in
theorem kernel_bound (q : TestSpace levels ξ) :
    ‖∫ y, w y * realize levels ξ q (Φ y)‖ ≤ (∫ y, ‖w y‖) * ‖q‖ := by
  calc
    _ ≤ ∫ y, ‖w y * realize levels ξ q (Φ y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖w y‖ * ‖q‖ := by
      apply integral_mono (kernel_integrable levels ξ w hw Φ hΦ q).norm
        (hw.norm.mul_const ‖q‖)
      intro y
      calc
        _ = ‖w y‖ * ‖realize levels ξ q (Φ y)‖ := norm_mul _ _
        _ ≤ ‖w y‖ * ‖q‖ :=
          mul_le_mul_of_nonneg_left (test_bound levels ξ q (Φ y)) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

def functional : TestSpace levels ξ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun q := ∫ y, w y * realize levels ξ q (Φ y)
      map_add' := by
        intro q r
        simp only [map_add, BoundedContinuousFunction.add_apply, mul_add]
        exact integral_add (kernel_integrable levels ξ w hw Φ hΦ q)
          (kernel_integrable levels ξ w hw Φ hΦ r)
      map_smul' := by
        intro c q
        simp only [map_smul, BoundedContinuousFunction.smul_apply, smul_eq_mul]
        simp_rw [mul_left_comm (w _) c]
        exact integral_const_mul _ _ }
    (∫ y, ‖w y‖) (kernel_bound levels ξ w hw Φ hΦ)

theorem functional_apply (q : TestSpace levels ξ) :
    functional levels ξ w hw Φ hΦ q = ∫ y, w y * realize levels ξ q (Φ y) := rfl

theorem functional_norm : ‖functional levels ξ w hw Φ hΦ‖ ≤ ∫ y, ‖w y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _)
  exact kernel_bound levels ξ w hw Φ hΦ

theorem ext_generators {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L M : TestSpace levels ξ →L[ℂ] E)
    (h : ∀ i, L (generator levels ξ i) = M (generator levels ξ i)) : L = M := by
  apply ContinuousLinearMap.ext_on (finite_core_dense levels ξ)
  rintro _ ⟨i, rfl⟩
  exact h i

end OperatorDerivativeRewrite.Foundation.FourierPathKernelFunctionals
