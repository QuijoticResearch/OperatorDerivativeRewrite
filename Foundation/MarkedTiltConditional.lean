import Foundation.ComplexRootTiltedExpectation

/-! Genuine conditional weighted transitions of the constructed complex jump process. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.MarkedTiltConditional
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedConditionalPolynomial MarkedPastReconstruction
open MarkedOperatorConditional MarkedHolomorphicExponential MarkedExponentialMartingale
open ComplexRootTransitionOperator (Test)

theorem weighted_observable_integrable (a ξ : ℝ) (t : ℝ≥0) (f : Test) :
    Integrable (fun ω => normalized a ξ t ω * f (process a t ω)) probability :=
  (normalized_integrable a ξ t).mul_bdd
    (f.continuous.measurable.comp (process_measurable a t)).aestronglyMeasurable
    (Eventually.of_forall fun _ω => f.norm_coe_le_norm _)

theorem conditional_transition (a ξ : ℝ) (s t : ℝ≥0) (hst : s ≤ t) (f : Test) :
    probability[fun ω => normalized a ξ t ω * f (process a t ω) | history a s] =ᵐ[probability]
      fun ω => normalized a ξ s ω *
        ComplexRootTiltedSemigroup.transition a ξ (t-s : ℝ≥0) f (process a s ω) := by
  let F : PastPath s × ℂ → ℂ := fun p => Complex.exp (-(t : ℂ)*symbol a ξ) *
    Complex.exp (Complex.I*(ξ : ℂ)*(p.1 ⟨s,by simp⟩+p.2)) * f (p.1 ⟨s,by simp⟩+p.2)
  have hmadd : Measurable (fun p : PastPath s × ℂ => p.1 ⟨s,by simp⟩+p.2) :=
    ((measurable_pi_apply (⟨s,by simp⟩ : Set.Iic s)).comp measurable_fst).add measurable_snd
  have hm : Measurable F :=
    (measurable_const.mul ((measurable_const.mul hmadd).cexp)).mul
      (f.continuous.measurable.comp hmadd)
  have hfun : (fun ω => F (pastPath a s ω,increment a s t ω)) =
      (fun ω => normalized a ξ t ω * f (process a t ω)) := by
    funext ω
    have hx : (pastPath a s ω) ⟨s,by simp⟩ + increment a s t ω = process a t ω := by
      change process a s ω + (process a t ω - process a s ω) = _
      abel
    change Complex.exp (-(t : ℂ)*symbol a ξ) *
      Complex.exp (Complex.I*(ξ : ℂ)*((pastPath a s ω) ⟨s,by simp⟩+increment a s t ω)) *
      f ((pastPath a s ω) ⟨s,by simp⟩+increment a s t ω) = _
    rw [hx]
    rfl
  have hi : Integrable (fun ω => F (pastPath a s ω,increment a s t ω)) probability := by
    rw [hfun]
    exact weighted_observable_integrable a ξ t f
  have he := IndependentInnovationConditioning.conditional_integral probability
    (pastPath a s) (increment a s t) (pastPath_measurable a s)
    (increment_measurable a s t) (past_increment_independent a s t hst)
    F hm.stronglyMeasurable hi
  rw [hfun,← history_eq_past,increment_law a s t hst] at he
  have ht : ((t-s : ℝ≥0) : ℂ) = (t : ℂ)-(s : ℂ) := by
    rw [NNReal.coe_sub hst]
    push_cast
    rfl
  have hc : Complex.exp (-(t : ℂ)*symbol a ξ) =
      Complex.exp (-(s : ℂ)*symbol a ξ) *
        Complex.exp (-((t-s : ℝ≥0) : ℂ)*symbol a ξ) := by
    rw [← Complex.exp_add, ht]
    congr 1
    ring
  filter_upwards [he] with ω he
  rw [he, ComplexRootTiltedSemigroup.transition_average_apply,
    ComplexRootTiltedExpectation.average_compound_expectation]
  have hiF : (fun y => F (pastPath a s ω,y)) =
      (fun y => (normalized a ξ s ω * Complex.exp (-((t-s : ℝ≥0) : ℂ)*symbol a ξ)) *
        (Complex.exp (Complex.I*(ξ : ℂ)*y) * f (process a s ω+y))) := by
    funext y
    change Complex.exp (-(t : ℂ)*symbol a ξ) *
      Complex.exp (Complex.I*(ξ : ℂ)*(process a s ω+y)) * f (process a s ω+y) = _
    rw [hc, mul_add, Complex.exp_add]
    unfold normalized phase
    ring
  rw [hiF, integral_const_mul]
  ring

end OperatorDerivativeRewrite.Foundation.MarkedTiltConditional
