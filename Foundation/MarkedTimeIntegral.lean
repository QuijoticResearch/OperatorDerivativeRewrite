import Foundation.RightContinuousProgressive
import Foundation.ConditionalBochnerFubini
import Foundation.MarkedOperatorConditional
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Genuine adapted pathwise time integrals of bounded observables of the marked process. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MarkedTimeIntegral
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale
attribute [local irreducible] MarkedRootRenewalProcess.process

theorem process_rightContinuous (a : ℝ) (ω : StateSample) :
    IsRightContinuous (fun t : ℝ≥0 => process a t ω) := by
  intro t
  have hr := (MarkedRootRenewalProcess.process_cadlag a ω).isRightContinuous (t : ℝ)
  exact hr.comp NNReal.continuous_coe.continuousWithinAt (fun r h => h)

theorem process_progressive (a : ℝ) : IsStronglyProgressive (history a) (process a) :=
  RightContinuousProgressive.progressive (history a) (process a) (process_adapted a)
    (process_rightContinuous a)

def stoppedValue (a : ℝ) (f : ComplexRootTransitionOperator.Test) (T : ℝ≥0)
    (p : StateSample × ℝ) : ℂ := f (process a (min p.2.toNNReal T) p.1)

theorem stoppedValue_past (a : ℝ) (f : ComplexRootTransitionOperator.Test) (T : ℝ≥0) :
    StronglyMeasurable[(history a T).prod inferInstance] (stoppedValue a f T) := by
  let : MeasurableSpace StateSample := history a T
  change StronglyMeasurable[(history a T).prod inferInstance]
    (fun p : StateSample × ℝ => f (process a (min p.2.toNNReal T) p.1))
  have htime : Measurable (fun p : StateSample × ℝ => min p.2.toNNReal T) :=
    (measurable_real_toNNReal.comp measurable_snd).min measurable_const
  have ht : Measurable (fun p : StateSample × ℝ =>
      (⟨min p.2.toNNReal T,by simp⟩ : Iic T)) := htime.subtype_mk
  have hx : Measurable (fun p : StateSample × ℝ =>
      ((⟨min p.2.toNNReal T,by simp⟩ : Iic T),p.1)) :=
    ht.prodMk measurable_fst
  have hp := (process_progressive a T).measurable
  simpa only [Function.comp_def,stoppedValue] using
    (f.continuous.measurable.comp (hp.comp hx)).stronglyMeasurable

theorem stoppedValue_measurable (a : ℝ) (f : ComplexRootTransitionOperator.Test) (T : ℝ≥0) :
    Measurable (stoppedValue a f T) := by
  change Measurable (fun p : StateSample × ℝ => f (process a (min p.2.toNNReal T) p.1))
  have hm : Measurable (fun p : StateSample × ℝ =>
      (((min p.2.toNNReal T : ℝ≥0) : ℝ),p.1)) := by fun_prop
  simpa only [stoppedValue,process,Function.comp_def] using
    f.continuous.measurable.comp ((MarkedRootRenewalProcess.process_joint_measurable a).comp hm)

theorem stoppedValue_bound (a : ℝ) (f : ComplexRootTransitionOperator.Test) (T : ℝ≥0)
    (p : StateSample × ℝ) : ‖stoppedValue a f T p‖ ≤ ‖f‖ := f.norm_coe_le_norm _

def primitive (a : ℝ) (f : ComplexRootTransitionOperator.Test) (T : ℝ≥0)
    (ω : StateSample) : ℂ := ∫ r in Ioc 0 (T : ℝ), stoppedValue a f T (ω,r)

theorem primitive_adapted (a : ℝ) (f : ComplexRootTransitionOperator.Test) :
    StronglyAdapted (history a) (primitive a f) := by
  intro T
  let : MeasurableSpace StateSample := history a T
  exact (stoppedValue_past a f T).integral_prod_right'

theorem stoppedValue_integrable (a : ℝ) (f : ComplexRootTransitionOperator.Test) (T : ℝ≥0) :
    Integrable (stoppedValue a f T) (probability.prod (volume.restrict (Ioc 0 (T : ℝ)))) := by
  apply Integrable.of_bound (stoppedValue_measurable a f T).aestronglyMeasurable ‖f‖
  exact Eventually.of_forall (stoppedValue_bound a f T)

theorem primitive_integrable (a : ℝ) (f : ComplexRootTransitionOperator.Test) (T : ℝ≥0) :
    Integrable (primitive a f T) probability :=
  (stoppedValue_integrable a f T).integral_prod_left

theorem primitive_eq_interval (a : ℝ) (f : ComplexRootTransitionOperator.Test)
    (T : ℝ≥0) (ω : StateSample) :
    primitive a f T ω = ∫ r in 0..(T : ℝ), f (process a r.toNNReal ω) := by
  rw [primitive,intervalIntegral.integral_of_le T.coe_nonneg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  simp only [stoppedValue,min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hr.2)]

theorem realTime_measurable (a : ℝ) (f : ComplexRootTransitionOperator.Test) (ω : StateSample) :
    Measurable (fun r : ℝ => f (process a r.toNNReal ω)) := by
  have hm : Measurable (fun r : ℝ => (((r.toNNReal : ℝ≥0) : ℝ),ω)) := by fun_prop
  simpa only [process,Function.comp_def] using
    f.continuous.measurable.comp ((MarkedRootRenewalProcess.process_joint_measurable a).comp hm)

theorem realTime_intervalIntegrable (a : ℝ) (f : ComplexRootTransitionOperator.Test)
    (ω : StateSample) (s t : ℝ) :
    IntervalIntegrable (fun r : ℝ => f (process a r.toNNReal ω)) volume s t := by
  constructor <;> exact Integrable.of_bound (realTime_measurable a f ω).aestronglyMeasurable ‖f‖
    (Eventually.of_forall (fun r => f.norm_coe_le_norm _))

theorem primitive_continuous (a : ℝ) (f : ComplexRootTransitionOperator.Test) (ω : StateSample) :
    Continuous (fun T : ℝ≥0 => primitive a f T ω) := by
  have hc := (intervalIntegral.continuous_primitive (realTime_intervalIntegrable a f ω) 0).comp
    NNReal.continuous_coe
  simpa only [Function.comp_def,← primitive_eq_interval a f] using hc

end OperatorDerivativeRewrite.Foundation.MarkedTimeIntegral
