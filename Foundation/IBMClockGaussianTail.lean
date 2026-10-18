import Foundation.IBMQuarticClockTerminal
import Foundation.GaussianCore
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The actual clock Gaussian law and a genuine standard Gaussian tail
integral for the half-line heat-potential construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockGaussianTail
open InfiniteGaussian IBMConstructedSources

theorem clock_hasLaw (T : ℝ≥0) : HasLaw (fun ω => clockPath ω T) (gaussianReal 0 T) gaussianProduct :=
  (GaussianTimeProcess.process_hasLaw T).congr (clockPath_coordinate_ae T)

theorem clock_density_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : StronglyMeasurable f) (T : ℝ≥0) (hT : T ≠ 0) :
    (∫ ω, f (clockPath ω T) ∂gaussianProduct) =
      ∫ r, gaussianPDFReal 0 T r • f r := by
  have he := integral_map (clock_hasLaw T).aemeasurable hf.aestronglyMeasurable
  rw [(clock_hasLaw T).map_eq] at he
  exact he.symm.trans (integral_gaussianReal_eq_integral_smul hT)

def density (r : ℝ) : ℝ := gaussianPDFReal 0 1 r

theorem density_continuous : Continuous density :=
  continuous_iff_continuousAt.mpr fun r => (GaussianCore.density_hasDerivAt r).continuousAt

theorem density_integrable : Integrable density := integrable_gaussianPDFReal _ _

theorem density_hasDerivAt (r : ℝ) : HasDerivAt density (-r*density r) r :=
  GaussianCore.density_hasDerivAt r

def tail (r : ℝ) : ℝ := ∫ x in Set.Ioi r, density x

theorem tail_primitive (r : ℝ) : tail r = tail 0 - ∫ x in 0..r, density x := by
  have he := intervalIntegral.integral_Ioi_sub_Ioi' (density_integrable.integrableOn (s := Set.Ioi (0 : ℝ)))
    (density_integrable.integrableOn (s := Set.Ioi r))
  change tail 0-tail r = _ at he
  linarith

theorem tail_hasDerivAt (r : ℝ) : HasDerivAt tail (-density r) r := by
  have he := (intervalIntegral.integral_hasDerivAt_right
    (density_continuous.intervalIntegrable 0 r) density_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    density_continuous.continuousAt).const_sub (tail 0)
  have hf : tail = fun y => tail 0 - ∫ x in 0..y, density x := funext tail_primitive
  rw [hf]
  exact he

theorem tail_continuous : Continuous tail :=
  continuous_iff_continuousAt.mpr fun r => (tail_hasDerivAt r).continuousAt

theorem tail_nonneg (r : ℝ) : 0 ≤ tail r :=
  integral_nonneg fun x => gaussianPDFReal_nonneg _ _ _

theorem tail_tendsto_zero : Tendsto tail atTop (𝓝 0) :=
  tendsto_integral_Ioi_zero tendsto_id

theorem tail_zero : tail 0 = 1/2 := by
  have hp : density = fun x : ℝ => (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(1/2 : ℝ)*x^2) := by
    funext x
    simp only [density, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    congr 2
    ring
  rw [tail, hp, integral_const_mul, integral_gaussian_Ioi]
  rw [show Real.pi/(1/2 : ℝ) = 2*Real.pi by ring]
  have hn : Real.sqrt (2*Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp

end OperatorDerivativeRewrite.Foundation.IBMClockGaussianTail
