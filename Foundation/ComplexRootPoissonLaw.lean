import Foundation.ComplexRootTransitionOperator
import Foundation.ComplexRootContinuousPaths
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Actual compound-root probability laws obtained by mixing genuine finite walks with Poisson counts. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonLaw
open ComplexFourthRootWalk

def weight (r : ℝ≥0) (n : ℕ) : ℝ := Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial

theorem weight_nonneg (r : ℝ≥0) (n : ℕ) : 0 ≤ weight r n := by unfold weight; positivity

theorem weight_hasSum (r : ℝ≥0) : HasSum (weight r) 1 := hasSum_one_poissonMeasure r

def law (r : ℝ≥0) (a : ℝ) : Measure ℂ :=
  (poissonMeasure r).bind (fun n => ComplexFourthRootWalk.law n a)

instance law_isProbability (r : ℝ≥0) (a : ℝ) : IsProbabilityMeasure (law r a) := by
  constructor
  rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
  simp

theorem law_sum (r : ℝ≥0) (a : ℝ) :
    law r a = Measure.sum (fun n => ENNReal.ofReal (weight r n) • ComplexFourthRootWalk.law n a) := by
  unfold law poissonMeasure
  rw [Measure.bind_sum _ _ (measurable_of_countable _).aemeasurable]
  congr 1
  funext n
  rw [Measure.bind_smul _ _ (measurable_of_countable _).aemeasurable,
    Measure.dirac_bind (measurable_of_countable _)]
  rfl

theorem walk_integral (n : ℕ) (a : ℝ) (f : ℂ →ᵇ ℂ) :
    (∫ z, f z ∂ComplexFourthRootWalk.law n a) =
      ∫ ω, f (terminal n a ω) ∂probability n := by
  rw [ComplexFourthRootWalk.law, integral_map (terminal_measurable n a).aemeasurable
    f.continuous.aestronglyMeasurable]

theorem count_expectation_integrable (r : ℝ≥0) (a : ℝ) (f : ℂ →ᵇ ℂ) :
    Integrable (fun n => ∫ z, f z ∂ComplexFourthRootWalk.law n a) (poissonMeasure r) := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ‖f‖
  exact Eventually.of_forall (fun n => by
    simpa using norm_integral_le_of_norm_le_const
      (μ := ComplexFourthRootWalk.law n a) (Eventually.of_forall f.norm_coe_le_norm))

theorem integral_bounded (r : ℝ≥0) (a : ℝ) (f : ℂ →ᵇ ℂ) :
    (∫ z, f z ∂law r a) = ∫ n, (∫ ω, f (terminal n a ω) ∂probability n) ∂poissonMeasure r := by
  have hi := f.integrable (μ := law r a)
  rw [law_sum] at hi
  rw [law_sum, integral_sum_measure hi]
  simp_rw [integral_smul_measure, ENNReal.toReal_ofReal (weight_nonneg r _)]
  have he := integral_poissonMeasure' (count_expectation_integrable r a f)
  simp_rw [weight, walk_integral] at he ⊢
  exact he.symm

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonLaw
