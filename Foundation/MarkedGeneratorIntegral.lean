import Foundation.MarkedIntegralConditioning
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The actual generator drift integral equals the transition-operator increment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.MarkedGeneratorIntegral
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedIntegralConditioning
open ComplexRootTransitionOperator ComplexRootPoissonSemigroup

theorem scalar_hasDerivAt (a : ℝ) (f : Test) (z : ℂ) (s r : ℝ) :
    HasDerivAt (fun q => transition a (q-s) f z)
      (transition a (r-s) (generator 1 a f) z) r := by
  let ev : (Test →L[ℂ] Test) →L[ℝ] ℂ :=
    ((BoundedContinuousFunction.evalCLM ℂ z).comp
      (ContinuousLinearMap.apply ℂ Test f)).restrictScalars ℝ
  have hs : HasDerivAt (fun q : ℝ => q-s) 1 r := by
    simpa only [id_eq] using (hasDerivAt_id r).sub_const s
  have hd := (transition_hasDerivAt a (r-s)).scomp r hs
  have he := ev.hasFDerivAt.comp_hasDerivAt r hd
  simpa [ev,generator,ContinuousLinearMap.comp_apply,Function.comp_def] using he

theorem generator_time_integral (a : ℝ) (f : Test) (z : ℂ) (s t : ℝ) :
    (∫ r in s..t, transition a (r-s) (generator 1 a f) z) = transition a (t-s) f z-f z := by
  have hc : Continuous (fun r : ℝ => transition a (r-s) (generator 1 a f) z) :=
    (BoundedContinuousFunction.evalCLM ℂ z).continuous.comp
      ((ContinuousLinearMap.apply ℂ Test (generator 1 a f)).continuous.comp
        ((transition_continuous a).comp (continuous_id.sub continuous_const)))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => scalar_hasDerivAt a f z s r) (hc.intervalIntegrable s t)
  simpa only [sub_self,transition_zero,ContinuousLinearMap.id_apply] using he

theorem prediction_generator_integral (a : ℝ) (f : Test) (s t : ℝ≥0) (hst : s ≤ t)
    (ω : StateSample) :
    (∫ r in Ioc (s : ℝ) (t : ℝ), prediction a (generator 1 a f) s (ω,r)) =
      transition a (t-s : ℝ≥0) f (process a s ω)-f (process a s ω) := by
  have htime (r : ℝ) (hr : r ∈ Ioc (s : ℝ) (t : ℝ)) :
      ((r.toNNReal-s : ℝ≥0) : ℝ) = r-(s : ℝ) := by
    have hr0 : 0 ≤ r := s.coe_nonneg.trans hr.1.le
    have hsr : s ≤ r.toNNReal := by
      exact_mod_cast (hr.1.le.trans (Real.le_coe_toNNReal r))
    rw [NNReal.coe_sub hsr,Real.coe_toNNReal r hr0]
  have hi : (∫ r in Ioc (s : ℝ) (t : ℝ), prediction a (generator 1 a f) s (ω,r)) =
      ∫ r in (s : ℝ)..(t : ℝ), transition a (r-(s : ℝ)) (generator 1 a f) (process a s ω) := by
    rw [intervalIntegral.integral_of_le (show (s : ℝ) ≤ (t : ℝ) from hst)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    simp only [prediction,htime r hr]
  rw [hi,generator_time_integral,NNReal.coe_sub hst]

end OperatorDerivativeRewrite.Foundation.MarkedGeneratorIntegral
