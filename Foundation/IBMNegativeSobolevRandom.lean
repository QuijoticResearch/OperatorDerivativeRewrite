import Foundation.IBMNegativeSobolevBounded
import Foundation.IBMSourceLaws

/-! Bochner-L² transfer of spatial distributional differentiation on the
independent Gaussian clock factor. -/
noncomputable section
open MeasureTheory
open scoped BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMNegativeSobolevRandom
open InfiniteGaussian IBMNegativeSobolevBounded

/-- Apply the verified spatial L²-to-H⁻¹ derivative to each clock sample.
This acts on Bochner L² equivalence classes, not pointwise representatives. -/
def randomDerivativeCLM :
    Lp (Lp ℂ 2 (volume : Measure ℝ)) 2 gaussianProduct →L[ℂ]
      Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct :=
  l2DerivativeCLM.compLpL 2 gaussianProduct

/-- The random-field operator has no larger norm than its spatial operator. -/
theorem randomDerivative_opNorm_le :
    ‖randomDerivativeCLM‖ ≤ ‖l2DerivativeCLM‖ :=
  l2DerivativeCLM.norm_compLpL_le

/-- Almost every clock sample carries the expected spatial H⁻¹ derivative. -/
theorem randomDerivative_apply_ae
    (u : Lp (Lp ℂ 2 (volume : Measure ℝ)) 2 gaussianProduct) :
    ∀ᵐ ω ∂gaussianProduct,
      (randomDerivativeCLM u) ω = l2DerivativeCLM (u ω) :=
  l2DerivativeCLM.coeFn_compLpL u

/-- Strong Bochner-L² convergence of spatial kernels passes to H⁻¹ after
distributional differentiation. -/
theorem randomDerivative_tendsto
    {u : ℕ → Lp (Lp ℂ 2 (volume : Measure ℝ)) 2 gaussianProduct}
    {v : Lp (Lp ℂ 2 (volume : Measure ℝ)) 2 gaussianProduct}
    (hu : Filter.Tendsto u Filter.atTop (nhds v)) :
    Filter.Tendsto (fun n => randomDerivativeCLM (u n)) Filter.atTop
      (nhds (randomDerivativeCLM v)) :=
  randomDerivativeCLM.continuous.tendsto v |>.comp hu

end OperatorDerivativeRewrite.Foundation.IBMNegativeSobolevRandom
