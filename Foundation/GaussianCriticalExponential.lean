import Foundation.GaussianPastKernelTransport
import Foundation.GaussianRandomTerminalMeasure

/-! Normalized delayed Gaussian likelihoods can fail the Novikov exponential-moment criterion. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianCriticalExponential
open GaussianCore GaussianRandomDensityKernel GaussianPastKernelTransport
  InfiniteGaussian GaussianTimeProcess GaussianRandomTerminalMeasure
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def critical (x : ℝ) : ℝ := Real.exp (x^2/2)

theorem critical_measurable : Measurable critical := by
  unfold critical
  fun_prop

theorem critical_positive (x : ℝ) : 0 < critical x := Real.exp_pos _

theorem pdf_cancellation (x : ℝ) :
    gaussianPDFReal 0 1 x * critical x = (Real.sqrt (2*Real.pi))⁻¹ := by
  simp only [gaussianPDFReal, critical, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  have he : -(x^2)/2+x^2/2=0 := by ring
  rw [he, Real.exp_zero, mul_one]

theorem critical_lintegral : (∫⁻ x, ENNReal.ofReal (critical x) ∂γ) = ∞ := by
  rw [γ, gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1)
    critical_measurable.ennreal_ofReal]
  simp only [Pi.mul_apply, gaussianPDF]
  simp_rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 _), pdf_cancellation]
  rw [lintegral_const, Real.volume_univ]
  exact ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))

theorem critical_not_integrable : ¬ Integrable critical γ := by
  intro h
  have he := ofReal_integral_eq_lintegral_ofReal h
    (Filter.Eventually.of_forall (fun x => (critical_positive x).le))
  rw [critical_lintegral] at he
  exact ENNReal.ofReal_ne_top he

def linearPair (p : ℝ × ℝ) : ℝ := kernel p.1 p.2

theorem linearPair_measurable : Measurable linearPair :=
  kernel_continuous.measurable

theorem linearPair_normalized :
    (∫⁻ p, ENNReal.ofReal (linearPair p) ∂γ.prod γ) = 1 :=
  normalized_lintegral γ id measurable_id

def linearDensity (ω : SampleSpace) : ℝ :=
  kernel (process 1 ω) (process 2 ω-process 1 ω)

theorem linearDensity_measurable : Measurable linearDensity :=
  linearPair_measurable.comp
    ((process_stronglyMeasurable 1).measurable.prodMk
      ((process_stronglyMeasurable 2).measurable.sub (process_stronglyMeasurable 1).measurable))

theorem linearDensity_positive (ω : SampleSpace) : 0 < linearDensity ω := kernel_positive _ _

theorem linearDensity_normalized :
    (∫⁻ ω, ENNReal.ofReal (linearDensity ω) ∂gaussianProduct) = 1 := by
  calc
    _ = ∫⁻ p, ENNReal.ofReal (linearPair p) ∂γ.prod γ :=
      joint_law.lintegral_comp linearPair_measurable.ennreal_ofReal.aemeasurable
    _ = 1 := linearPair_normalized

theorem actual_critical_lintegral :
    (∫⁻ ω, ENNReal.ofReal (critical (process 1 ω)) ∂gaussianProduct) = ∞ := by
  calc
    _ = ∫⁻ x, ENNReal.ofReal (critical x) ∂γ :=
      (process_hasLaw 1).lintegral_comp critical_measurable.ennreal_ofReal.aemeasurable
    _ = ∞ := critical_lintegral

theorem actual_critical_not_integrable :
    ¬ Integrable (fun ω => critical (process 1 ω)) gaussianProduct := by
  intro h
  have he := ofReal_integral_eq_lintegral_ofReal h
    (Filter.Eventually.of_forall (fun ω => (critical_positive (process 1 ω)).le))
  rw [actual_critical_lintegral] at he
  exact ENNReal.ofReal_ne_top he

end OperatorDerivativeRewrite.Foundation.GaussianCriticalExponential
