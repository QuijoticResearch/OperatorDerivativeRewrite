import Foundation.IndependentInnovationConditioning
import Foundation.MarkedConditionalPolynomial

/-! The constructed continuous-time process realizes the full verified transition operator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.MarkedOperatorConditional
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedConditionalPolynomial MarkedPastReconstruction

theorem history_eq_past (a : ℝ) (s : ℝ≥0) :
    history a s = MeasurableSpace.comap (pastPath a s) inferInstance := by
  rw [history,Filtration.natural_eq_comap]
  rfl

theorem past_increment_independent (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    IndepFun (pastPath a s) (increment a s t) probability := by
  change Indep (MeasurableSpace.comap (pastPath a s) inferInstance)
    (MeasurableSpace.comap (increment a s t) inferInstance) probability
  rw [← history_eq_past]
  exact (difference_independent_past a s t hst).symm

theorem observable_integrable (a : ℝ) (t : ℝ≥0) (f : ComplexRootTransitionOperator.Test) :
    Integrable (fun ω => f (process a t ω)) probability := by
  apply Integrable.of_bound (f.continuous.measurable.comp
    (process_measurable a t)).aestronglyMeasurable ‖f‖
  exact Eventually.of_forall (fun ω => f.norm_coe_le_norm _)

theorem conditional_transition (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t)
    (f : ComplexRootTransitionOperator.Test) :
    probability[fun ω => f (process a t ω) | history a s] =ᵐ[probability]
      fun ω => ComplexRootPoissonSemigroup.transition a (t-s : ℝ≥0) f (process a s ω) := by
  let F : PastPath s × ℂ → ℂ := fun p => f (p.1 ⟨s,by simp⟩+p.2)
  have hm : Measurable F := f.continuous.measurable.comp
    (((measurable_pi_apply (⟨s,by simp⟩ : Set.Iic s)).comp measurable_fst).add measurable_snd)
  have hfun : (fun ω => F (pastPath a s ω,increment a s t ω)) =
      (fun ω => f (process a t ω)) := by
    funext ω
    dsimp only [F,pastPath,increment,process]
    congr 1
    abel
  have hi : Integrable (fun ω => F (pastPath a s ω,increment a s t ω)) probability := by
    rw [hfun]
    exact observable_integrable a t f
  have he := IndependentInnovationConditioning.conditional_integral probability
    (pastPath a s) (increment a s t) (pastPath_measurable a s)
    (increment_measurable a s t) (past_increment_independent a s t hst)
    F hm.stronglyMeasurable hi
  rw [hfun,← history_eq_past,increment_law a s t hst] at he
  filter_upwards [he] with ω he
  rw [he,ComplexRootPoissonSemigroup.transition_law]
  rfl

end OperatorDerivativeRewrite.Foundation.MarkedOperatorConditional
