import Foundation.MarkedExponentialMartingale
import Mathlib.Probability.Independence.Integration

/-! Actual integrable two-time holomorphic transforms, with no characteristic-function claim. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedTwoTimeHolomorphicTransform
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedConditionalPolynomial MarkedHolomorphicExponential

def futurePhase (a ξ : ℝ) (s t : ℝ≥0) (ω : StateSample) : ℂ :=
  Complex.exp (Complex.I*(ξ : ℂ)*increment a s t ω)

theorem futurePhase_measurable (a ξ : ℝ) (s t : ℝ≥0) :
    Measurable (futurePhase a ξ s t) :=
  (measurable_const.mul (increment_measurable a s t)).cexp

theorem futurePhase_integrable (a ξ : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    Integrable (futurePhase a ξ s t) probability := by
  have hm : Measurable (fun z : ℂ => Complex.exp (Complex.I*(ξ : ℂ)*z)) := by fun_prop
  have hi : Integrable (fun z : ℂ => Complex.exp (Complex.I*(ξ : ℂ)*z))
      (probability.map (increment a s t)) := by
    rw [increment_law a s t hst]
    exact ComplexRootPoissonTransform.exponential_integrable (t-s) a ξ
  exact (integrable_map_measure hm.aestronglyMeasurable
    (increment_measurable a s t).aemeasurable).mp hi

theorem futurePhase_mean (a ξ : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, futurePhase a ξ s t ω ∂probability) =
      Complex.exp (((t-s : ℝ≥0) : ℂ)*symbol a ξ) := by
  have hm : Measurable (fun z : ℂ => Complex.exp (Complex.I*(ξ : ℂ)*z)) := by fun_prop
  have he := integral_map (μ := probability) (increment_measurable a s t).aemeasurable
    hm.aestronglyMeasurable
  rw [increment_law a s t hst,ComplexRootPoissonTransform.transform] at he
  exact he.symm

theorem phase_future_independent (a η ξ : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    IndepFun (phase a η s) (futurePhase a ξ s t) probability := by
  have hm : Measurable[MeasurableSpace.comap (increment a s t) inferInstance]
      (futurePhase a ξ s t) :=
    (measurable_const.mul (comap_measurable (increment a s t))).cexp
  exact indep_of_indep_of_le (difference_independent_past a s t hst).symm
    (phase_adapted a η s).measurable.comap_le hm.comap_le

theorem product_factorization (a η ξ : ℝ) (s t : ℝ≥0) (ω : StateSample) :
    phase a η s ω*phase a ξ t ω = phase a (η+ξ) s ω*futurePhase a ξ s t ω := by
  unfold phase futurePhase increment
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem product_integrable (a η ξ : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    Integrable (fun ω => phase a η s ω*phase a ξ t ω) probability := by
  have he : (fun ω => phase a η s ω*phase a ξ t ω) =
      (fun ω => phase a (η+ξ) s ω*futurePhase a ξ s t ω) :=
    funext (product_factorization a η ξ s t)
  rw [he]
  exact (phase_future_independent a (η+ξ) ξ s t hst).integrable_mul
    (phase_integrable a (η+ξ) s) (futurePhase_integrable a ξ s t hst)

theorem two_time_transform (a η ξ : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, phase a η s ω*phase a ξ t ω ∂probability) =
      Complex.exp ((s : ℂ)*symbol a (η+ξ)+((t-s : ℝ≥0) : ℂ)*symbol a ξ) := by
  simp_rw [product_factorization]
  rw [(phase_future_independent a (η+ξ) ξ s t hst).integral_fun_mul_eq_mul_integral
    (phase_integrable a (η+ξ) s).aestronglyMeasurable
    (futurePhase_integrable a ξ s t hst).aestronglyMeasurable,
    phase_mean,futurePhase_mean a ξ s t hst,Complex.exp_add]

end OperatorDerivativeRewrite.Foundation.MarkedTwoTimeHolomorphicTransform
