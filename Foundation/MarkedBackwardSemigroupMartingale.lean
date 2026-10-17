import Foundation.MarkedOperatorConditional

/-! Explicit backward semigroup martingales on the actual continuous-time natural filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.MarkedBackwardSemigroupMartingale
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedOperatorConditional ComplexRootPoissonSemigroup

def backward (a : ℝ) (T : ℝ≥0) (f : ComplexRootTransitionOperator.Test)
    (t : ℝ≥0) (ω : StateSample) : ℂ := transition a (T-t : ℝ≥0) f (process a (min t T) ω)

theorem backward_adapted (a : ℝ) (T : ℝ≥0) (f : ComplexRootTransitionOperator.Test) :
    StronglyAdapted (history a) (backward a T f) := by
  intro t
  have hp := (process_adapted a (min t T)).mono ((history a).mono (min_le_left t T))
  exact ((transition a (T-t : ℝ≥0) f).continuous.measurable.comp hp.measurable).stronglyMeasurable

theorem backward_integrable (a : ℝ) (T t : ℝ≥0) (f : ComplexRootTransitionOperator.Test) :
    Integrable (backward a T f t) probability :=
  observable_integrable a (min t T) (transition a (T-t : ℝ≥0) f)

theorem terminal_condExp (a : ℝ) (T t : ℝ≥0) (f : ComplexRootTransitionOperator.Test) :
    probability[fun ω => f (process a T ω) | history a t] =ᵐ[probability] backward a T f t := by
  by_cases ht : t ≤ T
  · have hb : backward a T f t =
        (fun ω => transition a (T-t : ℝ≥0) f (process a t ω)) := by
      funext ω
      simp only [backward,min_eq_left ht]
    rw [hb]
    exact conditional_transition a t T ht f
  · have hT : T ≤ t := le_of_not_ge ht
    have hp := (process_adapted a T).mono ((history a).mono hT)
    have hm := (f.continuous.measurable.comp hp.measurable).stronglyMeasurable
    have he := condExp_of_stronglyMeasurable (μ := probability) ((history a).le t)
      hm (observable_integrable a T f)
    have hb : backward a T f t = (fun ω => f (process a T ω)) := by
      funext ω
      simp only [backward,min_eq_right hT,tsub_eq_zero_of_le hT,NNReal.coe_zero,
        transition_zero,ContinuousLinearMap.id_apply]
    rw [hb]
    exact Filter.EventuallyEq.of_eq he

theorem backward_martingale (a : ℝ) (T : ℝ≥0) (f : ComplexRootTransitionOperator.Test) :
    Martingale (backward a T f) (history a) probability :=
  (martingale_condExp (fun ω => f (process a T ω)) (history a) probability).congr
    (backward_adapted a T f) (fun t => terminal_condExp a T t f)

theorem backward_after_terminal (a : ℝ) (T t : ℝ≥0) (hT : T ≤ t)
    (f : ComplexRootTransitionOperator.Test) (ω : StateSample) :
    backward a T f t ω = f (process a T ω) := by
  simp only [backward,min_eq_right hT,tsub_eq_zero_of_le hT,NNReal.coe_zero,
    transition_zero,ContinuousLinearMap.id_apply]

end OperatorDerivativeRewrite.Foundation.MarkedBackwardSemigroupMartingale
