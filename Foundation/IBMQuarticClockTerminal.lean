import Foundation.IBMQuarticSpatialWeakLimit
import Foundation.IBMClockSixthMoment

/-! Actual clock averages of the quartic primitive, as source Gaussian-L²
objects. The unresolved drift-plus-origin identification is not assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticClockTerminal
open InfiniteGaussian IBMQuarticSecondPrimitive IBMQuarticPrimitiveLimit
open IBMConstructedSources IBMClockSixthMoment

theorem clockPosition_measurable (T : ℝ≥0) : Measurable (fun ω => |clockPath ω T|) :=
  continuous_abs.measurable.comp ((continuous_eval_const T).measurable.comp clockPath_measurable)

theorem polynomial_bound (x : ℝ) : (|x|+2)^2 ≤ 4*(1+|x|)^3 := by
  nlinarith [abs_nonneg x, sq_nonneg |x|, pow_nonneg (abs_nonneg x) 3]

theorem majorant_integrable (T : ℝ≥0) :
    Integrable (fun ω => 4*(1+|clockPath ω T|)^3) gaussianProduct :=
  ((IBMClockCubicJointL2.clock_cubic_growth_memLp T).integrable (by norm_num)).const_mul 4

theorem terminal_integrable (n : ℕ) (T : ℝ≥0) :
    Integrable (fun ω => primitive n |clockPath ω T|) gaussianProduct := by
  apply (majorant_integrable T).mono'
    ((primitive_continuous n).stronglyMeasurable.comp_measurable (clockPosition_measurable T)).aestronglyMeasurable
  exact Eventually.of_forall fun ω =>
    (primitive_bound n _).trans (by simpa only [abs_abs] using polynomial_bound (clockPath ω T))

theorem terminalLimit_integrable (T : ℝ≥0) :
    Integrable (fun ω => primitiveLimit |clockPath ω T|) gaussianProduct := by
  apply (majorant_integrable T).mono'
    (primitiveLimit_continuous.stronglyMeasurable.comp_measurable (clockPosition_measurable T)).aestronglyMeasurable
  exact Eventually.of_forall fun ω =>
    (primitiveLimit_bound _).trans (by simpa only [abs_abs] using polynomial_bound (clockPath ω T))

def terminalMean (n : ℕ) (T : ℝ≥0) : GaussianL2 :=
  ∫ ω, primitive n |clockPath ω T| ∂gaussianProduct

def terminalLimit (T : ℝ≥0) : GaussianL2 :=
  ∫ ω, primitiveLimit |clockPath ω T| ∂gaussianProduct

theorem terminalMean_tendsto (T : ℝ≥0) :
    Tendsto (fun n => terminalMean n T) atTop (𝓝 (terminalLimit T)) := by
  apply tendsto_integral_of_dominated_convergence (fun ω => 4*(1+|clockPath ω T|)^3)
  · intro n
    exact (terminal_integrable n T).aestronglyMeasurable
  · exact majorant_integrable T
  · intro n
    exact Eventually.of_forall fun ω =>
      (primitive_bound n _).trans (by simpa only [abs_abs] using polynomial_bound (clockPath ω T))
  · exact Eventually.of_forall fun ω => primitive_tendsto |clockPath ω T|

theorem primitiveLimit_zero : primitiveLimit 0 = 0 := by simp [primitiveLimit]

/-- The actual terminal-minus-initial candidate converges in source L².
Equality with the full clock-averaged correction remains separate. -/
theorem terminalDifference_tendsto (T : ℝ≥0) :
    Tendsto (fun n => terminalMean n T - primitive n 0) atTop (𝓝 (terminalLimit T)) := by
  simpa only [primitiveLimit_zero, sub_zero] using (terminalMean_tendsto T).sub (primitive_tendsto 0)

end OperatorDerivativeRewrite.Foundation.IBMQuarticClockTerminal
