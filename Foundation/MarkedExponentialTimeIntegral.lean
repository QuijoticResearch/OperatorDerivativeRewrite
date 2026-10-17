import Foundation.MarkedTimeIntegral
import Foundation.BandLimitedComplexExtension
import Foundation.PoissonEntireMoments

/-! Genuine adapted pathwise time integrals for continuous observables of exponential growth. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MarkedExponentialTimeIntegral
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale
attribute [local irreducible] MarkedRootRenewalProcess.process

def envelope (a B : ℝ) (T : ℝ≥0) (ω : StateSample) : ℝ :=
  Real.exp ((ExponentialRenewalCount.count T ω.1 : ℝ)*(B*(2*|a|)))

theorem process_norm_bound (a : ℝ) (t : ℝ≥0) (ω : StateSample) :
    ‖process a t ω‖ ≤ (ExponentialRenewalCount.count t ω.1 : ℝ)*(2*|a|) := by
  unfold MarkedRenewalMartingale.process MarkedRootRenewalProcess.process
  rw [RootRenewalWalkMarginal.position_eq_terminal]
  exact ComplexRootPoissonPolynomialDomain.terminal_norm_bound _ a _

theorem envelope_integrable (a B : ℝ) (T : ℝ≥0) : Integrable (envelope a B T) probability := by
  have hp : MeasurePreserving (fun ω : StateSample => ExponentialRenewalCount.count T ω.1)
      probability (poissonMeasure T) :=
    (RenewalCompensatedMartingale.count_preserving T).comp measurePreserving_fst
  have hm : Measurable (fun n : ℕ => Real.exp ((n : ℝ)*(B*(2*|a|)))) :=
    measurable_of_countable _
  have hi : Integrable (fun n : ℕ => Real.exp ((n : ℝ)*(B*(2*|a|))))
      (probability.map (fun ω : StateSample => ExponentialRenewalCount.count T ω.1)) := by
    rw [hp.map_eq]
    exact PoissonEntireMoments.exponential_integrable T _
  exact (integrable_map_measure hm.aestronglyMeasurable hp.measurable.aemeasurable).mp hi

theorem radial_envelope (a B : ℝ) (hB : 0 ≤ B) (s T : ℝ≥0) (hs : s ≤ T)
    (ω : StateSample) : Real.exp (B*‖process a s ω‖) ≤ envelope a B T ω := by
  apply Real.exp_le_exp.mpr
  have hc : (ExponentialRenewalCount.count s ω.1 : ℝ) ≤
      (ExponentialRenewalCount.count T ω.1 : ℝ) := by
    exact_mod_cast ExponentialRenewalCount.count_monotone ω.1 (show (s : ℝ) ≤ T from hs)
  calc
    _ ≤ B*((ExponentialRenewalCount.count s ω.1 : ℝ)*(2*|a|)) :=
      mul_le_mul_of_nonneg_left (process_norm_bound a s ω) hB
    _ ≤ B*((ExponentialRenewalCount.count T ω.1 : ℝ)*(2*|a|)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (by positivity)) hB
    _ = _ := by ring

def stoppedValue (a : ℝ) (F : ℂ → ℂ) (T : ℝ≥0) (p : StateSample × ℝ) : ℂ :=
  F (process a (min p.2.toNNReal T) p.1)

theorem stoppedValue_past (a : ℝ) (F : ℂ → ℂ) (hF : Continuous F) (T : ℝ≥0) :
    StronglyMeasurable[(history a T).prod inferInstance] (stoppedValue a F T) := by
  let : MeasurableSpace StateSample := history a T
  change StronglyMeasurable[(history a T).prod inferInstance]
    (fun p : StateSample × ℝ => F (process a (min p.2.toNNReal T) p.1))
  have htime : Measurable (fun p : StateSample × ℝ => min p.2.toNNReal T) :=
    (measurable_real_toNNReal.comp measurable_snd).min measurable_const
  have ht : Measurable (fun p : StateSample × ℝ =>
      (⟨min p.2.toNNReal T,by simp⟩ : Iic T)) := htime.subtype_mk
  have hx : Measurable (fun p : StateSample × ℝ =>
      ((⟨min p.2.toNNReal T,by simp⟩ : Iic T),p.1)) := ht.prodMk measurable_fst
  have hp := (MarkedTimeIntegral.process_progressive a T).measurable
  simpa only [Function.comp_def, stoppedValue] using
    (hF.measurable.comp (hp.comp hx)).stronglyMeasurable

theorem stoppedValue_measurable (a : ℝ) (F : ℂ → ℂ) (hF : Continuous F) (T : ℝ≥0) :
    Measurable (stoppedValue a F T) := by
  change Measurable (fun p : StateSample × ℝ => F (process a (min p.2.toNNReal T) p.1))
  have hm : Measurable (fun p : StateSample × ℝ =>
      (((min p.2.toNNReal T : ℝ≥0) : ℝ),p.1)) := by fun_prop
  simpa only [stoppedValue, process, Function.comp_def] using
    hF.measurable.comp ((MarkedRootRenewalProcess.process_joint_measurable a).comp hm)

theorem stoppedValue_integrable (a : ℝ) (F : ℂ → ℂ) (hF : Continuous F)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ z, ‖F z‖ ≤ A*Real.exp (B*‖z‖)) (T : ℝ≥0) :
    Integrable (stoppedValue a F T) (probability.prod (volume.restrict (Ioc 0 (T : ℝ)))) := by
  have hi := ((envelope_integrable a B T).const_mul A).mul_prod
    (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 (T : ℝ))))
  apply hi.mono' (stoppedValue_measurable a F hF T).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖F (process a (min p.2.toNNReal T) p.1)‖ ≤ (A*envelope a B T p.1)*1
    rw [mul_one]
    exact (hbound _).trans (mul_le_mul_of_nonneg_left
      (radial_envelope a B hB _ T (min_le_right _ _) p.1) hA)

def primitive (a : ℝ) (F : ℂ → ℂ) (T : ℝ≥0) (ω : StateSample) : ℂ :=
  ∫ r in Ioc 0 (T : ℝ), stoppedValue a F T (ω,r)

theorem primitive_adapted (a : ℝ) (F : ℂ → ℂ) (hF : Continuous F) :
    StronglyAdapted (history a) (primitive a F) := by
  intro T
  let : MeasurableSpace StateSample := history a T
  exact (stoppedValue_past a F hF T).integral_prod_right'

theorem primitive_integrable (a : ℝ) (F : ℂ → ℂ) (hF : Continuous F)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ z, ‖F z‖ ≤ A*Real.exp (B*‖z‖)) (T : ℝ≥0) :
    Integrable (primitive a F T) probability :=
  (stoppedValue_integrable a F hF A B hA hB hbound T).integral_prod_left

theorem primitive_eq_interval (a : ℝ) (F : ℂ → ℂ) (T : ℝ≥0) (ω : StateSample) :
    primitive a F T ω = ∫ r in 0..(T : ℝ), F (process a r.toNNReal ω) := by
  rw [primitive, intervalIntegral.integral_of_le T.coe_nonneg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  simp only [stoppedValue, min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hr.2)]

theorem band_primitive_integrable (R : ℝ≥0) (φ : ℝ → ℂ)
    (hφ : Integrable φ (BandLimitedComplexExtension.band R)) (a : ℝ) (T : ℝ≥0) :
    Integrable (primitive a (BandLimitedComplexExtension.extension R φ) T) probability :=
  primitive_integrable a _ (BandLimitedComplexExtension.extension_continuous R φ hφ)
    (∫ ξ, ‖φ ξ‖ ∂BandLimitedComplexExtension.band R) R
    (integral_nonneg fun _ => norm_nonneg _) R.coe_nonneg
    (BandLimitedComplexExtension.norm_bound R φ hφ) T

end OperatorDerivativeRewrite.Foundation.MarkedExponentialTimeIntegral
