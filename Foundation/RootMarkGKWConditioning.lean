import Foundation.RootMarkFiniteRange
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! Conditional-expectation interpretation of the actual stochastic GKW projection. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal InnerProductSpace
namespace OperatorDerivativeRewrite.Foundation.RootMarkGKWConditioning
open RootMarkStochasticIntegral RootMarkFiniteOperator RootMarkFiniteRange RootMarkGKWProjection
open MarkedRootRenewalProcess (MarkSample marks)

def conditionalValue (N : ℕ) (Y : Lp ℂ 2 marks) : Lp ℂ 2 marks :=
  condExpL2 ℂ ℂ (history.le N) Y

theorem conditionalValue_mean (N : ℕ) (Y : Lp ℂ 2 marks) :
    (∫ η, conditionalValue N Y η ∂marks) = ∫ η, Y η ∂marks := by
  have he := integral_condExpL2_eq_of_fin_meas_real (hm := history.le N) Y
    (s := Set.univ) MeasurableSet.univ (measure_ne_top _ _)
  simpa only [conditionalValue, Measure.restrict_univ] using he

theorem projection_eq_conditionalValue (a : ℝ) (ha : a ≠ 0) (N : ℕ)
    (Y : Lp ℂ 2 marks) (hmean : (∫ η, Y η ∂marks) = 0) :
    projection a N Y = conditionalValue N Y := by
  have hm := aestronglyMeasurable_condExpL2 (E := ℂ) (𝕜 := ℂ) (history.le N) Y
  have hr := (range_measurable a ha N (conditionalValue N Y)).mpr
    ⟨(conditionalValue_mean N Y).trans hmean,hm⟩
  change (predictableRange a N : Submodule ℂ (Lp ℂ 2 marks)).starProjection Y = _
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hr
  intro w hw
  obtain ⟨u,rfl⟩ := hw
  have hu := ((range_measurable a ha N (finiteIntegral a N u)).mp ⟨u,rfl⟩).2
  have he := inner_condExpL2_eq_inner_fun (𝕜 := ℂ) (history.le N) Y (finiteIntegral a N u) hu
  rw [inner_sub_left]
  exact sub_eq_zero.mpr he.symm

end OperatorDerivativeRewrite.Foundation.RootMarkGKWConditioning
