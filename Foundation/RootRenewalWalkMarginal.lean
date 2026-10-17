import Foundation.MarkedRootRenewalProcess
import Foundation.ComplexRootPoissonSemigroup

/-! The actual infinite marks have the previously verified finite-walk marginals. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.RootRenewalWalkMarginal
open MarkedRootRenewalProcess

def initialSegment (n : ℕ) (η : MarkSample) : ComplexFourthRootWalk.Sample n := fun i => η i

theorem prefix_measurable (n : ℕ) : Measurable (initialSegment n) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)

theorem prefix_preserving (n : ℕ) :
    MeasurePreserving (initialSegment n) marks (ComplexFourthRootWalk.probability n) := by
  refine ⟨prefix_measurable n, ?_⟩
  change marks.map (fun η (i : Fin n) => η i.val) =
    Measure.pi (fun _ : Fin n => ComplexFourthRootNoise.probability)
  have hi := marks_independent.precomp (g := fun i : Fin n => i.val) Fin.val_injective
  have he := hi.map_fun_eq_pi_map
    (fun i => (measurable_pi_apply i.val).aemeasurable)
  simpa only [(mark_preserving _).map_eq] using he

theorem position_eq_terminal (a : ℝ) (n : ℕ) (η : MarkSample) :
    position a n η = ComplexFourthRootWalk.terminal n a (initialSegment n η) := by
  simp only [position, ComplexFourthRootWalk.terminal,
    ComplexFourthRootWalk.increment, initialSegment]
  exact (Fin.sum_univ_eq_sum_range _ n).symm

theorem position_law (a : ℝ) (n : ℕ) :
    marks.map (position a n) = ComplexFourthRootWalk.law n a := by
  have he : position a n = ComplexFourthRootWalk.terminal n a ∘ initialSegment n :=
    funext (position_eq_terminal a n)
  rw [he,
    ← Measure.map_map (ComplexFourthRootWalk.terminal_measurable n a) (prefix_measurable n),
    (prefix_preserving n).map_eq]
  rfl

theorem position_integral (a : ℝ) (n : ℕ) (f : ℂ →ᵇ ℂ) (z : ℂ) :
    (∫ η, f (z + position a n η) ∂marks) =
      ((ComplexRootTransitionOperator.step a)^n) f z := by
  rw [ComplexRootPoissonSemigroup.step_pow_apply]
  let F : ℂ → ℂ := fun y => f (z+y)
  have hm : Measurable F := f.continuous.measurable.comp (measurable_const.add measurable_id)
  have he := congrArg (fun μ : Measure ℂ => ∫ y, F y ∂μ) (position_law a n)
  rw [integral_map (position_measurable a n).aemeasurable hm.aestronglyMeasurable,
    ComplexFourthRootWalk.law,
    integral_map (ComplexFourthRootWalk.terminal_measurable n a).aemeasurable
      hm.aestronglyMeasurable] at he
  exact he

end OperatorDerivativeRewrite.Foundation.RootRenewalWalkMarginal
