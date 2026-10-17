import Foundation.MarkedTimeIntegral

/-! Conditioning actual future pathwise time integrals by the verified operator semigroup. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.MarkedIntegralConditioning
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedOperatorConditional MarkedTimeIntegral
open ComplexRootTransitionOperator ComplexRootPoissonSemigroup
attribute [local irreducible] MarkedRootRenewalProcess.process

def value (a : ℝ) (f : Test) (p : StateSample × ℝ) : ℂ := f (process a p.2.toNNReal p.1)

theorem value_measurable (a : ℝ) (f : Test) : Measurable (value a f) := by
  change Measurable (fun p : StateSample × ℝ => f (process a p.2.toNNReal p.1))
  have hm : Measurable (fun p : StateSample × ℝ => (((p.2.toNNReal : ℝ≥0) : ℝ),p.1)) :=
    (measurable_coe_nnreal_real.comp (measurable_real_toNNReal.comp measurable_snd)).prodMk
      measurable_fst
  simpa only [process,Function.comp_def] using
    f.continuous.measurable.comp ((MarkedRootRenewalProcess.process_joint_measurable a).comp hm)

def prediction (a : ℝ) (f : Test) (s : ℝ≥0) (p : StateSample × ℝ) : ℂ :=
  transition a (p.2.toNNReal-s : ℝ≥0) f (process a s p.1)

theorem transition_evaluation_continuous (a : ℝ) (f : Test) (s : ℝ≥0) :
    Continuous (fun p : ℝ × ℂ => transition a (p.1.toNNReal-s : ℝ≥0) f p.2) := by
  have ht : Continuous (fun r : ℝ => transition a (r.toNNReal-s : ℝ≥0) f) :=
    (ContinuousLinearMap.apply ℂ Test f).continuous.comp ((transition_continuous a).comp
      (NNReal.continuous_coe.comp (continuous_real_toNNReal.sub continuous_const)))
  have he : Continuous (fun p : Test × ℂ => p.1 p.2) := continuous_eval
  exact he.comp (ht.prodMap continuous_id)

theorem prediction_past (a : ℝ) (f : Test) (s : ℝ≥0) :
    StronglyMeasurable[(history a s).prod inferInstance] (prediction a f s) := by
  change StronglyMeasurable[(history a s).prod inferInstance]
    (fun p : StateSample × ℝ => transition a (p.2.toNNReal-s : ℝ≥0) f (process a s p.1))
  let : MeasurableSpace StateSample := history a s
  have hm : Measurable (fun p : StateSample × ℝ => (p.2,process a s p.1)) :=
    measurable_snd.prodMk ((process_adapted a s).measurable.comp measurable_fst)
  simpa only [Function.comp_def] using
    ((transition_evaluation_continuous a f s).measurable.comp hm).stronglyMeasurable

theorem prediction_measurable (a : ℝ) (f : Test) (s : ℝ≥0) : Measurable (prediction a f s) := by
  change Measurable
    (fun p : StateSample × ℝ => transition a (p.2.toNNReal-s : ℝ≥0) f (process a s p.1))
  have hm : Measurable (fun p : StateSample × ℝ => (p.2,process a s p.1)) :=
    measurable_snd.prodMk ((process_measurable a s).comp measurable_fst)
  simpa only [Function.comp_def] using (transition_evaluation_continuous a f s).measurable.comp hm

theorem transition_bound (a : ℝ) (f : Test) (h : ℝ≥0) (z : ℂ) :
    ‖transition a h f z‖ ≤ ‖f‖ := by
  rw [transition_law]
  simpa using norm_integral_le_of_norm_le_const (μ := ComplexRootPoissonLaw.law h a)
    (Eventually.of_forall (fun y => f.norm_coe_le_norm (z+y)))

theorem value_integrable (a : ℝ) (f : Test) (s t : ℝ≥0) :
    Integrable (value a f) (probability.prod (volume.restrict (Ioc (s : ℝ) (t : ℝ)))) := by
  exact Integrable.of_bound (value_measurable a f).aestronglyMeasurable ‖f‖
    (Eventually.of_forall (fun p => f.norm_coe_le_norm _))

theorem prediction_integrable (a : ℝ) (f : Test) (s t : ℝ≥0) :
    Integrable (prediction a f s) (probability.prod (volume.restrict (Ioc (s : ℝ) (t : ℝ)))) := by
  exact Integrable.of_bound (prediction_measurable a f s).aestronglyMeasurable ‖f‖
    (Eventually.of_forall (fun p => transition_bound a f _ _))

theorem future_integral_condExp (a : ℝ) (f : Test) (s t : ℝ≥0) :
    probability[fun ω => ∫ r in Ioc (s : ℝ) (t : ℝ), value a f (ω,r) | history a s]
      =ᵐ[probability] fun ω => ∫ r in Ioc (s : ℝ) (t : ℝ), prediction a f s (ω,r) := by
  apply ConditionalBochnerFubini.conditional_integral (history a s) probability
    (volume.restrict (Ioc (s : ℝ) (t : ℝ))) ((history a).le s) (value a f) (prediction a f s)
    (value_integrable a f s t) (prediction_integrable a f s t) (prediction_past a f s)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have hsr : s ≤ r.toNNReal := by
    exact_mod_cast (hr.1.le.trans (Real.le_coe_toNNReal r))
  exact conditional_transition a s r.toNNReal hsr f

theorem primitive_increment (a : ℝ) (f : Test) (s t : ℝ≥0) (ω : StateSample) :
    primitive a f t ω-primitive a f s ω = ∫ r in (s : ℝ)..(t : ℝ), value a f (ω,r) := by
  rw [primitive_eq_interval,primitive_eq_interval]
  exact intervalIntegral.integral_interval_sub_left (realTime_intervalIntegrable a f ω 0 t)
    (realTime_intervalIntegrable a f ω 0 s)

end OperatorDerivativeRewrite.Foundation.MarkedIntegralConditioning
