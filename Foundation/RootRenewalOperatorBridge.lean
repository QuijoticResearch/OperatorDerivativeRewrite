import Foundation.RootRenewalWalkMarginal
import Foundation.RootRenewalPathLaw

/-! Actual renewal marginals and their bounded-test operator, without assuming Poisson counts. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction NNReal
namespace OperatorDerivativeRewrite.Foundation.RootRenewalOperatorBridge
open MarkedRootRenewalProcess ComplexRootTransitionOperator

local instance : Nontrivial Test := ⟨⟨BoundedContinuousFunction.const ℂ 0,
    BoundedContinuousFunction.const ℂ 1, by
      intro h
      have he := congrArg (fun f : Test => f 0) h
      norm_num at he⟩⟩

local instance : NormOneClass (Test →L[ℂ] Test) := ⟨ContinuousLinearMap.norm_id⟩

def countLaw (t : ℝ) : Measure ℕ :=
  ExponentialHoldingSequence.probability.map (ExponentialRenewalCount.count t)

instance countLaw_probability (t : ℝ) : IsProbabilityMeasure (countLaw t) := by
  unfold countLaw
  infer_instance

theorem process_law (a t : ℝ) :
    probability.map (process a t) =
      (countLaw t).bind (fun n => ComplexFourthRootWalk.law n a) := by
  ext s hs
  rw [Measure.map_apply (process_measurable a t) hs, probability,
    Measure.prod_apply ((process_measurable a t) hs),
    Measure.bind_apply hs (measurable_of_countable _).aemeasurable, countLaw,
    lintegral_map (measurable_of_countable _) (ExponentialRenewalCount.count_measurable t)]
  apply lintegral_congr
  intro ω
  rw [← RootRenewalWalkMarginal.position_law,
    Measure.map_apply (position_measurable a _) hs]
  rfl

theorem powers_integrable (a t : ℝ) :
    Integrable (fun n : ℕ => (step a)^n) (countLaw t) := by
  apply Integrable.of_bound StronglyMeasurable.of_discrete.aestronglyMeasurable 1
  exact Eventually.of_forall (fun n =>
    (norm_pow_le (step a) n).trans
      (by simpa using pow_le_pow_left₀ (norm_nonneg (step a)) (step_norm a) n))

def transition (a t : ℝ) : Test →L[ℂ] Test := ∫ n : ℕ, (step a)^n ∂countLaw t

theorem transition_norm (a t : ℝ) : ‖transition a t‖ ≤ 1 := by
  unfold transition
  simpa using norm_integral_le_of_norm_le_const (μ := countLaw t)
    (Eventually.of_forall (fun n : ℕ =>
      (norm_pow_le (step a) n).trans
        (by simpa using pow_le_pow_left₀ (norm_nonneg (step a)) (step_norm a) n)))

theorem transition_apply (a t : ℝ) (f : Test) (z : ℂ) :
    transition a t f z = ∫ n : ℕ, ((step a)^n) f z ∂countLaw t := by
  let ev : (Test →L[ℂ] Test) →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ z).comp (ContinuousLinearMap.apply ℂ Test f)
  change ev (∫ n : ℕ, (step a)^n ∂countLaw t) =
    ∫ n : ℕ, ev ((step a)^n) ∂countLaw t
  exact (ev.integral_comp_comm (powers_integrable a t)).symm

theorem process_integrable (a t : ℝ) (f : Test) (z : ℂ) :
    Integrable (fun ω => f (z + process a t ω)) probability := by
  apply Integrable.of_bound
    (f.continuous.measurable.comp (measurable_const.add
      (process_measurable a t))).aestronglyMeasurable ‖f‖
  exact Eventually.of_forall (fun ω => f.norm_coe_le_norm _)

theorem transition_process (a t : ℝ) (f : Test) (z : ℂ) :
    transition a t f z = ∫ ω, f (z + process a t ω) ∂probability := by
  rw [transition_apply, probability,
    integral_prod _ (process_integrable a t f z)]
  simp_rw [process, RootRenewalWalkMarginal.position_integral]
  exact integral_map (ExponentialRenewalCount.count_measurable t).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable

theorem transition_eq_poisson_of_countLaw (a t : ℝ) (r : ℝ≥0)
    (h : countLaw t = poissonMeasure r) :
    transition a t = ComplexRootPoissonSemigroup.transition a r := by
  rw [transition, h, ComplexRootPoissonSemigroup.transition_average]

theorem process_law_eq_poisson_of_countLaw (a t : ℝ) (r : ℝ≥0)
    (h : countLaw t = poissonMeasure r) :
    probability.map (process a t) = ComplexRootPoissonLaw.law r a := by
  rw [process_law, h]
  rfl

end OperatorDerivativeRewrite.Foundation.RootRenewalOperatorBridge
