import Foundation.IBMQuarticHeatFubini

/-! Direct actual-law reuse for reflected clock means on proved Bochner
domains. This does not identify unreflected mixed-source kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMReflectedClockMean
open InfiniteGaussian IBMClockGaussianTail IBMClockHeatPotential IBMQuarticHeatHalfLine
open IBMConstructedSources

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem reflected_density_integrable (f : ℝ → E) (hf : StronglyMeasurable f)
    (T : ℝ≥0) (hT : 0 < T)
    (hi : Integrable (fun ω => f |clockPath ω T|) gaussianProduct) :
    Integrable (fun r => heatKernel T r • f |r|) := by
  have hm := hf.comp_measurable continuous_abs.measurable
  have hg : Integrable (fun r => f |r|) (gaussianReal 0 T) := by
    rw [← (clock_hasLaw T).map_eq]
    exact (integrable_map_measure hm.aestronglyMeasurable (clock_hasLaw T).aemeasurable).mpr hi
  rw [gaussianReal_of_var_ne_zero 0 (ne_of_gt hT)] at hg
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hg
  simp only [toReal_gaussianPDF] at hg
  convert hg using 1
  funext r
  rw [heatKernel_eq_pdf (NNReal.coe_pos.mpr hT)]
  rfl

theorem reflected_clock_integral (f : ℝ → E) (hf : StronglyMeasurable f)
    (T : ℝ≥0) (hT : 0 < T)
    (hi : Integrable (fun ω => f |clockPath ω T|) gaussianProduct) :
    (∫ ω, f |clockPath ω T| ∂gaussianProduct) =
      (2 : ℝ) • ∫ r in Ioi 0, heatKernel T r • f r := by
  have hh : (∫ ω, f |clockPath ω T| ∂gaussianProduct) =
      ∫ r, heatKernel T r • f |r| :=
    clock_heat_integral (fun r => f |r|) (hf.comp_measurable continuous_abs.measurable) T hT
  rw [hh]
  let F : ℝ → E := fun r => heatKernel T r • f |r|
  have hF : Integrable F := reflected_density_integrable f hf T hT hi
  have hn : (fun r => F (-r)) = F := by
    funext r
    simp only [F, heatKernel_even, abs_neg]
  have he : (∫ r in Iic (0 : ℝ), F r) = ∫ r in Ioi 0, F r := by
    simpa only [neg_zero, hn] using (integral_comp_neg_Ioi (0 : ℝ) F).symm
  have hp : (∫ r in Ioi (0 : ℝ), F r) = ∫ r in Ioi 0, heatKernel T r • f r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [F, abs_of_pos (show 0 < r from hr)]
  change (∫ r, F r) = _
  rw [← integral_add_compl measurableSet_Ioi hF, compl_Ioi, he, hp]
  module

end OperatorDerivativeRewrite.Foundation.IBMReflectedClockMean
