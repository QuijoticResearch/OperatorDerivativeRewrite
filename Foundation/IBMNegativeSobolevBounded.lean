import Foundation.IBMNegativeSobolev
import Mathlib.Analysis.Normed.Operator.Banach

/-! Continuity of the deterministic L²-to-H⁻¹ spatial derivative. -/
noncomputable section
open MeasureTheory TemperedDistribution
open scoped BesselPotentialSpace SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.IBMNegativeSobolevBounded
open IBMNegativeSobolev

/-- The canonical continuous embedding of H⁻¹ into tempered distributions. -/
def hminusOneToDistrCLM : H^{(-1 : ℝ)}(ℝ) →L[ℂ] 𝓢'(ℝ, ℂ) :=
  (besselPotential ℝ ℂ (1 : ℝ)).comp
    ((Lp.toTemperedDistributionCLM ℂ volume 2).comp
      ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).toContinuousLinearEquiv.toContinuousLinearMap))

@[simp] theorem hminusOneToDistrCLM_apply (v : H^{(-1 : ℝ)}(ℝ)) :
    hminusOneToDistrCLM v = v.toDistr := by
  dsimp [hminusOneToDistrCLM]
  change (besselPotential ℝ ℂ 1) v.toLp = v.toDistr
  simpa using (BesselPotentialSpace.besselPotential_neg_toLp_eq (f := v))

/-- The derivative map has a sequentially closed graph: both the L² and
H⁻¹ embeddings into tempered distributions are continuous there. -/
theorem l2Derivative_seqClosedGraph :
    ∀ (u : ℕ → Lp ℂ 2 (volume : Measure ℝ))
      (x : Lp ℂ 2 (volume : Measure ℝ)) (y : H^{(-1 : ℝ)}(ℝ)),
      Filter.Tendsto u Filter.atTop (nhds x) →
      Filter.Tendsto (l2DerivativeLinear ∘ u) Filter.atTop (nhds y) →
      y = l2DerivativeLinear x := by
  intro u x y hu hv
  apply BesselPotentialSpace.ext
  have hleft := (hminusOneToDistrCLM.continuous.tendsto y).comp hv
  have hright := ((LineDeriv.lineDerivOpCLM ℂ (𝓢'(ℝ, ℂ)) (1 : ℝ)).comp
    (Lp.toTemperedDistributionCLM ℂ volume 2)).continuous.tendsto x |>.comp hu
  have heq : ∀ n, hminusOneToDistrCLM (l2DerivativeLinear (u n)) =
      LineDeriv.lineDerivOpCLM ℂ (𝓢'(ℝ, ℂ)) (1 : ℝ)
        (Lp.toTemperedDistributionCLM ℂ volume 2 (u n)) := by
    intro n
    simp [l2DerivativeLinear, l2Derivative_toDistr]
  have hright' : Filter.Tendsto
      (fun n => hminusOneToDistrCLM (l2DerivativeLinear (u n)))
      Filter.atTop
      (nhds (LineDeriv.lineDerivOpCLM ℂ (𝓢'(ℝ, ℂ)) (1 : ℝ)
        (Lp.toTemperedDistributionCLM ℂ volume 2 x))) := by
    convert hright using 1
    · funext n
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using heq n
    · simp
  have hleft' : Filter.Tendsto
      (fun n => hminusOneToDistrCLM (l2DerivativeLinear (u n)))
      Filter.atTop (nhds (hminusOneToDistrCLM y)) := by
    simpa only [Function.comp_def] using hleft
  have hlim := tendsto_nhds_unique hleft' hright'
  simpa [hminusOneToDistrCLM_apply, l2DerivativeLinear,
    l2Derivative_toDistr] using hlim

/-- Bounded distributional differentiation from L²(ℝ) into H⁻¹(ℝ). -/
def l2DerivativeCLM : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] H^{(-1 : ℝ)}(ℝ) :=
  ContinuousLinearMap.ofSeqClosedGraph l2Derivative_seqClosedGraph

@[simp] theorem l2DerivativeCLM_apply (u : Lp ℂ 2 (volume : Measure ℝ)) :
    l2DerivativeCLM u = l2Derivative u := rfl

/-- The operator norm supplies a finite uniform L²-to-H⁻¹ bound. -/
theorem l2Derivative_norm_le (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖l2Derivative u‖ ≤ ‖l2DerivativeCLM‖ * ‖u‖ := by
  exact l2DerivativeCLM.le_opNorm u

end OperatorDerivativeRewrite.Foundation.IBMNegativeSobolevBounded
