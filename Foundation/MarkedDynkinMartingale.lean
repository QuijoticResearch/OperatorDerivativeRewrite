import Foundation.MarkedGeneratorIntegral

/-! Actual continuous-time Dynkin martingales with genuine adapted pathwise compensators. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.MarkedDynkinMartingale
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedOperatorConditional MarkedTimeIntegral
open MarkedIntegralConditioning MarkedGeneratorIntegral
open ComplexRootTransitionOperator ComplexRootPoissonSemigroup

theorem drift_increment_condExp (a : ℝ) (f : Test) (s t : ℝ≥0) (hst : s ≤ t) :
    probability[fun ω => primitive a (generator 1 a f) t ω-
      primitive a (generator 1 a f) s ω | history a s] =ᵐ[probability]
      fun ω => transition a (t-s : ℝ≥0) f (process a s ω)-f (process a s ω) := by
  have he := future_integral_condExp a (generator 1 a f) s t
  have hfun : (fun ω => primitive a (generator 1 a f) t ω-
      primitive a (generator 1 a f) s ω) =
      (fun ω => ∫ r in Ioc (s : ℝ) (t : ℝ), value a (generator 1 a f) (ω,r)) := by
    funext ω
    rw [primitive_increment,intervalIntegral.integral_of_le
      (show (s : ℝ) ≤ (t : ℝ) from hst)]
  rw [← hfun] at he
  filter_upwards [he] with ω he
  exact he.trans (prediction_generator_integral a f s t hst ω)

theorem observable_increment_condExp (a : ℝ) (f : Test) (s t : ℝ≥0) (hst : s ≤ t) :
    probability[fun ω => f (process a t ω)-f (process a s ω) | history a s] =ᵐ[probability]
      fun ω => transition a (t-s : ℝ≥0) f (process a s ω)-f (process a s ω) := by
  have he := condExp_sub (observable_integrable a t f) (observable_integrable a s f) (history a s)
  have hp : probability[fun ω => f (process a s ω) | history a s] =
      (fun ω => f (process a s ω)) := condExp_of_stronglyMeasurable ((history a).le s)
    (f.continuous.measurable.comp (process_adapted a s).measurable).stronglyMeasurable
    (observable_integrable a s f)
  rw [hp] at he
  have ht := conditional_transition a s t hst f
  filter_upwards [he,ht] with ω he ht
  calc
    _ = probability[fun ω => f (process a t ω) | history a s] ω-f (process a s ω) := he
    _ = _ := by rw [ht]

def dynkin (a : ℝ) (f : Test) (t : ℝ≥0) (ω : StateSample) : ℂ :=
  f (process a t ω)-f 0-primitive a (generator 1 a f) t ω

theorem dynkin_adapted (a : ℝ) (f : Test) : StronglyAdapted (history a) (dynkin a f) := by
  intro t
  exact ((f.continuous.measurable.comp (process_adapted a t).measurable).stronglyMeasurable.sub
    stronglyMeasurable_const).sub (primitive_adapted a (generator 1 a f) t)

theorem dynkin_integrable (a : ℝ) (f : Test) (t : ℝ≥0) :
    Integrable (dynkin a f t) probability :=
  ((observable_integrable a t f).sub (integrable_const (f 0))).sub
    (primitive_integrable a (generator 1 a f) t)

theorem dynkin_increment_condExp_zero (a : ℝ) (f : Test) (s t : ℝ≥0) (hst : s ≤ t) :
    probability[dynkin a f t-dynkin a f s | history a s] =ᵐ[probability] fun _ => 0 := by
  have hfun : dynkin a f t-dynkin a f s =
      ((fun ω => f (process a t ω))-(fun ω => f (process a s ω)))-
        (primitive a (generator 1 a f) t-primitive a (generator 1 a f) s) := by
    funext ω
    simp only [dynkin,Pi.sub_apply]
    ring
  have he := condExp_sub ((observable_integrable a t f).sub (observable_integrable a s f))
    ((primitive_integrable a (generator 1 a f) t).sub
      (primitive_integrable a (generator 1 a f) s)) (history a s)
  rw [← hfun] at he
  have ho := observable_increment_condExp a f s t hst
  have hd := drift_increment_condExp a f s t hst
  filter_upwards [he,ho,hd] with ω he ho hd
  calc
    _ = probability[fun ω => f (process a t ω)-f (process a s ω) | history a s] ω-
        probability[fun ω => primitive a (generator 1 a f) t ω-
          primitive a (generator 1 a f) s ω | history a s] ω := he
    _ = 0 := by rw [ho,hd]; ring

theorem dynkin_condExp (a : ℝ) (f : Test) (s t : ℝ≥0) (hst : s ≤ t) :
    probability[dynkin a f t | history a s] =ᵐ[probability] dynkin a f s := by
  have he := condExp_sub (dynkin_integrable a f t) (dynkin_integrable a f s) (history a s)
  have hp := condExp_of_stronglyMeasurable (μ := probability) ((history a).le s)
    (dynkin_adapted a f s) (dynkin_integrable a f s)
  rw [hp] at he
  have hz := dynkin_increment_condExp_zero a f s t hst
  filter_upwards [he,hz] with ω he hz
  change probability[dynkin a f t-dynkin a f s | history a s] ω =
    probability[dynkin a f t | history a s] ω-dynkin a f s ω at he
  exact sub_eq_zero.mp (he.symm.trans hz)

theorem dynkin_martingale (a : ℝ) (f : Test) :
    Martingale (dynkin a f) (history a) probability :=
  ⟨dynkin_adapted a f,fun s t hst => dynkin_condExp a f s t hst⟩

theorem dynkin_formula (a : ℝ) (f : Test) (t : ℝ≥0) (ω : StateSample) :
    dynkin a f t ω = f (process a t ω)-f 0-
      ∫ r in 0..(t : ℝ), (generator 1 a f) (process a r.toNNReal ω) := by
  rw [dynkin,primitive_eq_interval]

theorem dynkin_zero (a : ℝ) (f : Test) (ω : StateSample) : dynkin a f 0 ω = 0 := by
  simp [dynkin,primitive,process,MarkedRootRenewalProcess.process_zero]

theorem dynkin_mean (a : ℝ) (f : Test) (t : ℝ≥0) :
    (∫ ω, dynkin a f t ω ∂probability) = 0 := by
  calc
    _ = ∫ ω, probability[dynkin a f t | history a 0] ω ∂probability :=
      (integral_condExp ((history a).le 0)).symm
    _ = ∫ ω, dynkin a f 0 ω ∂probability :=
      integral_congr_ae (dynkin_condExp a f 0 t bot_le)
    _ = 0 := by simp only [dynkin_zero,integral_zero]

end OperatorDerivativeRewrite.Foundation.MarkedDynkinMartingale
