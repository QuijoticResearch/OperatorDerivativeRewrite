import Foundation.IBMDeltaBoundary

/-! Random H⁻¹ boundary distributions from square-integrable clock coefficients. -/
noncomputable section
open MeasureTheory
open scoped BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMRandomBoundary
open InfiniteGaussian IBMDeltaBoundary

/-- Multiplication of the concrete origin Dirac mass by a scalar coefficient. -/
def boundaryScalarCLM : ℂ →L[ℂ] H^{(-1 : ℝ)}(ℝ) :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) deltaZeroHminusOne

@[simp] theorem boundaryScalarCLM_apply (a : ℂ) :
    boundaryScalarCLM a = a • deltaZeroHminusOne := rfl

/-- A square-integrable clock coefficient defines a square-integrable
H⁻¹-valued random boundary distribution. -/
def randomBoundaryCLM :
    Lp ℂ 2 gaussianProduct →L[ℂ]
      Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct :=
  boundaryScalarCLM.compLpL 2 gaussianProduct

theorem randomBoundary_apply_ae (a : Lp ℂ 2 gaussianProduct) :
    ∀ᵐ ω ∂gaussianProduct,
      (randomBoundaryCLM a) ω = (a ω) • deltaZeroHminusOne := by
  change (randomBoundaryCLM a) =ᵐ[gaussianProduct]
    (fun ω => (a ω) • deltaZeroHminusOne)
  simpa only [randomBoundaryCLM, boundaryScalarCLM_apply] using
    boundaryScalarCLM.coeFn_compLpL a

theorem randomBoundary_tendsto
    {a : ℕ → Lp ℂ 2 gaussianProduct} {b : Lp ℂ 2 gaussianProduct}
    (ha : Filter.Tendsto a Filter.atTop (nhds b)) :
    Filter.Tendsto (fun n => randomBoundaryCLM (a n)) Filter.atTop
      (nhds (randomBoundaryCLM b)) :=
  randomBoundaryCLM.continuous.tendsto b |>.comp ha

end OperatorDerivativeRewrite.Foundation.IBMRandomBoundary
