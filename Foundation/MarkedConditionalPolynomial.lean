import Foundation.MarkedRenewalMartingale
import Foundation.ComplexRootLowerPolynomialMoments
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Independence.Integration

/-! Integrable mixed polynomial products and conditional pull-out for actual complex jumps. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedConditionalPolynomial
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale

def increment (a : ℝ) (s t : ℝ≥0) (ω : StateSample) : ℂ := process a t ω-process a s ω

theorem increment_measurable (a : ℝ) (s t : ℝ≥0) : Measurable (increment a s t) :=
  (process_measurable a t).sub (process_measurable a s)

theorem increment_law (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    probability.map (increment a s t) = ComplexRootPoissonLaw.law (t-s) a := by
  have he := MarkedPastFutureIndependence.increment_law a s (t-s)
  rw [add_tsub_cancel_of_le hst] at he
  exact he

theorem increment_power_integrable (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) (j : ℕ) :
    Integrable (fun ω => increment a s t ω^j) probability := by
  have hm : Measurable (fun z : ℂ => z^j) := by fun_prop
  have hi : Integrable (fun z : ℂ => z^j) (probability.map (increment a s t)) := by
    rw [increment_law a s t hst]
    exact ComplexRootPoissonPolynomialDomain.power_integrable (t-s) a j
  exact (integrable_map_measure hm.aestronglyMeasurable
    (increment_measurable a s t).aemeasurable).mp hi

theorem increment_power_mean (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) (j : ℕ) :
    (∫ ω, increment a s t ω^j ∂probability) =
      ∫ y : ℂ, y^j ∂ComplexRootPoissonLaw.law (t-s) a := by
  have hm : Measurable (fun z : ℂ => z^j) := by fun_prop
  have he := integral_map (μ := probability) (increment_measurable a s t).aemeasurable
    hm.aestronglyMeasurable
  rw [increment_law a s t hst] at he
  exact he.symm

theorem increment_power_condExp (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) (j : ℕ) :
    probability[fun ω => increment a s t ω^j | history a s] =ᵐ[probability]
      fun _ => ∫ y : ℂ, y^j ∂ComplexRootPoissonLaw.law (t-s) a := by
  have hm := (comap_measurable (increment a s t)).pow_const j
  have he := condExp_indep_eq (increment_measurable a s t).comap_le ((history a).le s)
    hm.stronglyMeasurable (difference_independent_past a s t hst)
  simpa only [increment_power_mean a s t hst j] using he

theorem past_increment_independent (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t)
    (f : StateSample → ℂ) (hf : StronglyMeasurable[history a s] f) (j : ℕ) :
    IndepFun f (fun ω => increment a s t ω^j) probability := by
  have hm := (comap_measurable (increment a s t)).pow_const j
  exact indep_of_indep_of_le (difference_independent_past a s t hst).symm
    hf.measurable.comap_le hm.comap_le

theorem past_mul_integrable (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t)
    (f : StateSample → ℂ) (hf : StronglyMeasurable[history a s] f)
    (hi : Integrable f probability) (j : ℕ) :
    Integrable (fun ω => f ω*increment a s t ω^j) probability :=
  (past_increment_independent a s t hst f hf j).integrable_mul hi
    (increment_power_integrable a s t hst j)

theorem past_mul_condExp (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t)
    (f : StateSample → ℂ) (hf : StronglyMeasurable[history a s] f)
    (hi : Integrable f probability) (j : ℕ) :
    probability[fun ω => f ω*increment a s t ω^j | history a s] =ᵐ[probability]
      fun ω => f ω*(∫ y : ℂ, y^j ∂ComplexRootPoissonLaw.law (t-s) a) := by
  have he := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hf
    (past_mul_integrable a s t hst f hf hi j) (increment_power_integrable a s t hst j)
  have hd := increment_power_condExp a s t hst j
  filter_upwards [he,hd] with ω he hd
  calc
    _ = f ω*probability[fun ω => increment a s t ω^j | history a s] ω := he
    _ = _ := by rw [hd]

theorem power_product_integrable (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) (c : ℂ) (k j : ℕ) :
    Integrable (fun ω => (c*process a s ω^k)*increment a s t ω^j) probability := by
  have hf := ((process_adapted a s).measurable.pow_const k).const_mul c
  exact past_mul_integrable a s t hst _ hf.stronglyMeasurable
    ((process_power_integrable a s k).const_mul c) j

theorem power_product_condExp (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) (c : ℂ) (k j : ℕ) :
    probability[fun ω => (c*process a s ω^k)*increment a s t ω^j | history a s] =ᵐ[probability]
      fun ω => (c*process a s ω^k)*(∫ y : ℂ, y^j ∂ComplexRootPoissonLaw.law (t-s) a) := by
  have hf := ((process_adapted a s).measurable.pow_const k).const_mul c
  exact past_mul_condExp a s t hst _ hf.stronglyMeasurable
    ((process_power_integrable a s k).const_mul c) j

end OperatorDerivativeRewrite.Foundation.MarkedConditionalPolynomial
