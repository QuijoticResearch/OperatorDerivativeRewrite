import Foundation.IBMNegativeSobolevRandom
import Foundation.IBMRandomBoundary

/-! Assembly of interior derivative and origin boundary channels in the IBM
first-scenery-chaos H⁻¹ target space. -/
noncomputable section
open MeasureTheory
open scoped BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMDualAssembly
open InfiniteGaussian IBMNegativeSobolevRandom IBMRandomBoundary

abbrev InteriorInput :=
  Lp (Lp ℂ 2 (volume : Measure ℝ)) 2 gaussianProduct
abbrev BoundaryInput := Lp ℂ 2 gaussianProduct
abbrev DualOutput := Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct

/-- Bounded assembly of the spatial derivative residual and the origin
boundary mass. It is a map on candidate kernels, not a claim that IBM's
actual correction has already been identified with these inputs. -/
def dualAssemblyCLM : InteriorInput × BoundaryInput →L[ℂ] DualOutput :=
  randomDerivativeCLM.comp (ContinuousLinearMap.fst ℂ InteriorInput BoundaryInput) +
    randomBoundaryCLM.comp (ContinuousLinearMap.snd ℂ InteriorInput BoundaryInput)

@[simp] theorem dualAssemblyCLM_apply (u : InteriorInput) (a : BoundaryInput) :
    dualAssemblyCLM (u, a) = randomDerivativeCLM u + randomBoundaryCLM a := rfl

/-- Separate quantitative control of the interior and boundary channels. -/
theorem dualAssembly_norm_le (u : InteriorInput) (a : BoundaryInput) :
    ‖dualAssemblyCLM (u, a)‖ ≤
      ‖randomDerivativeCLM‖ * ‖u‖ + ‖randomBoundaryCLM‖ * ‖a‖ := by
  rw [dualAssemblyCLM_apply]
  exact (norm_add_le _ _).trans
    (add_le_add (randomDerivativeCLM.le_opNorm u)
      (randomBoundaryCLM.le_opNorm a))

/-- Convergence of both input channels suffices for convergence of their
assembled H⁻¹-valued random field. -/
theorem dualAssembly_tendsto
    {u : ℕ → InteriorInput} {v : InteriorInput}
    {a : ℕ → BoundaryInput} {b : BoundaryInput}
    (hu : Filter.Tendsto u Filter.atTop (nhds v))
    (ha : Filter.Tendsto a Filter.atTop (nhds b)) :
    Filter.Tendsto (fun n => dualAssemblyCLM (u n, a n)) Filter.atTop
      (nhds (dualAssemblyCLM (v, b))) :=
  dualAssemblyCLM.continuous.tendsto (v, b) |>.comp (by
    simpa only [nhds_prod_eq] using hu.prodMk ha)

end OperatorDerivativeRewrite.Foundation.IBMDualAssembly
