import Foundation.IBMQuarticHeatEndpoint

/-! Actual reflected Gaussian terminal density and the radius limit of
the origin-corrected quartic heat integral. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticHeatHalfLine
open InfiniteGaussian IBMClockGaussianTail IBMClockHeatPotential IBMClockOriginMean
open IBMQuarticSecondPrimitive IBMQuarticPrimitiveLimit IBMQuarticClockTerminal
open IBMQuarticHeatEndpoint

theorem reflected_primitive_gaussian_integrable (n : ℕ) (T : ℝ≥0) :
    Integrable (fun r => primitive n |r|) (gaussianReal 0 T) := by
  rw [← (clock_hasLaw T).map_eq]
  apply (integrable_map_measure
    ((primitive_continuous n).comp continuous_abs).aestronglyMeasurable
    (clock_hasLaw T).aemeasurable).mpr
  exact terminal_integrable n T

theorem reflected_density_integrable (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    Integrable (fun r => heatKernel T r • primitive n |r|) := by
  have hi := reflected_primitive_gaussian_integrable n T
  rw [gaussianReal_of_var_ne_zero 0 (ne_of_gt hT)] at hi
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hi
  simp only [toReal_gaussianPDF] at hi
  convert hi using 1
  funext r
  rw [heatKernel_eq_pdf (NNReal.coe_pos.mpr hT)]
  rfl

theorem primitive_heat_integrableOn (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    IntegrableOn (fun r => heatKernel T r • primitive n r) (Ioi 0) := by
  apply (reflected_density_integrable n T hT).integrableOn.congr_fun _ measurableSet_Ioi
  intro r hr
  change heatKernel T r • primitive n |r| = heatKernel T r • primitive n r
  rw [abs_of_pos hr]

theorem heatKernel_even (T x : ℝ) : heatKernel T (-x) = heatKernel T x := by
  unfold heatKernel
  rw [neg_div, density_even]

/-- Genuine source-L2 reflected terminal mean, with its Bochner domain
transferred from the actual clock law. -/
theorem terminalMean_eq_halfline (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    terminalMean n T = (2 : ℝ) • ∫ r in Ioi 0, heatKernel T r • primitive n r := by
  have hh : (∫ ω, primitive n |IBMConstructedSources.clockPath ω T| ∂gaussianProduct) =
      ∫ r, heatKernel T r • primitive n |r| :=
    clock_heat_integral (fun r => primitive n |r|)
      ((primitive_continuous n).comp continuous_abs).stronglyMeasurable T hT
  rw [terminalMean, hh]
  let F : ℝ → GaussianL2 := fun r => heatKernel T r • primitive n |r|
  have hi : Integrable F := reflected_density_integrable n T hT
  have hn : (fun r => F (-r)) = F := by
    funext r
    simp only [F, heatKernel_even, abs_neg]
  have he : (∫ r in Iic (0 : ℝ), F r) = ∫ r in Ioi 0, F r := by
    simpa only [neg_zero, hn] using (integral_comp_neg_Ioi (0 : ℝ) F).symm
  have hp : (∫ r in Ioi (0 : ℝ), F r) = ∫ r in Ioi 0, heatKernel T r • primitive n r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [F, abs_of_pos (show 0 < r from hr)]
  change (∫ r, F r) = _
  rw [← integral_add_compl measurableSet_Ioi hi, compl_Ioi, he, hp]
  module

def truncatedCorrection (n : ℕ) (T : ℝ≥0) (R : ℝ) : GaussianL2 :=
  (∫ ω, BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct) • slope n 0 +
    (1/2 : ℝ) • (∫ r in 0..R, potential T r •
      GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n r))

/-- The actual origin-corrected spatial truncations converge to the actual
clock terminal mean. Identifying them with the time correction is separate. -/
theorem truncatedCorrection_tendsto (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (truncatedCorrection n T) atTop (𝓝 (terminalMean n T-primitive n 0)) := by
  have hi := intervalIntegral_tendsto_integral_Ioi 0 (primitive_heat_integrableOn n T hT) tendsto_id
  have he := ((hi.const_smul (2 : ℝ)).sub_const (primitive n 0)).add
    ((endpoint_tendsto_zero n (NNReal.coe_pos.mpr hT)).const_smul (1/2 : ℝ))
  have hf : truncatedCorrection n T = fun R =>
      (2 : ℝ) • (∫ r in 0..R, heatKernel T r • primitive n r) - primitive n 0 +
        (1/2 : ℝ) • IBMQuarticHeatBoundary.endpoint n T R :=
    funext (actual_origin_finite_cancellation n T hT)
  rw [hf]
  simpa only [id_eq, zero_smul, smul_zero, add_zero, ← terminalMean_eq_halfline n T hT] using he

end OperatorDerivativeRewrite.Foundation.IBMQuarticHeatHalfLine
