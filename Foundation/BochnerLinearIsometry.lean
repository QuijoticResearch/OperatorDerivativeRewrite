import Mathlib.MeasureTheory.Function.L2Space

/-! Pointwise lifting of genuine linear isometries to Bochner L2. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.BochnerLinearIsometry
variable {X E F : Type*} [MeasurableSpace X] (μ : Measure X)
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def lift (J : E →ₗᵢ[𝕜] F) : Lp E 2 μ →ₗᵢ[𝕜] Lp F 2 μ where
  toLinearMap := (J.toContinuousLinearMap.compLpL 2 μ).toLinearMap
  norm_map' u := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable u)
    filter_upwards [J.toContinuousLinearMap.coeFn_compLp u] with x hx
    change ‖J.toContinuousLinearMap.compLp u x‖ = ‖u x‖
    rw [hx]
    exact J.norm_map (u x)

theorem lift_coeFn (J : E →ₗᵢ[𝕜] F) (u : Lp E 2 μ) :
    lift μ J u =ᵐ[μ] fun x => J (u x) := J.toContinuousLinearMap.coeFn_compLp u

theorem lift_norm (J : E →ₗᵢ[𝕜] F) (u : Lp E 2 μ) : ‖lift μ J u‖ = ‖u‖ :=
  (lift μ J).norm_map u

theorem lift_eq_zero_iff (J : E →ₗᵢ[𝕜] F) (u : Lp E 2 μ) : lift μ J u = 0 ↔ u = 0 :=
  (lift μ J).injective.eq_iff' (map_zero _)

end OperatorDerivativeRewrite.Foundation.BochnerLinearIsometry
