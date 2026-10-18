import Foundation.MarkedRealizationMarkov
import Foundation.MarkedRenewalExponentialTransform

/-! Genuine unbounded holomorphic exponential martingales for actual finite marked-renewal laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedRealizationExponentialMartingale
open MarkedRenewalRealization MarkedRealizationMartingale
variable {A : Type*} [MeasurableSpace A]

def symbol (μ : Measure A) (z : A → ℂ) (w : ℂ) : ℂ :=
  MarkedRenewalExponentialTransform.oneStep μ z w-1

def phase (z : A → ℂ) (w : ℂ) (t : ℝ≥0) (ω : Sample A) : ℂ := Complex.exp (w*value z t ω)

theorem phase_adapted (z : A → ℂ) (hz : Measurable z) (w : ℂ) :
    StronglyAdapted (history z hz) (phase z w) := fun t =>
  ((measurable_const.mul (value_adapted z hz t).measurable).cexp).stronglyMeasurable

theorem phase_integrable (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (w : ℂ) (t : ℝ≥0) :
    Integrable (phase z w t) (probability μ) :=
  MarkedRenewalExponentialTransform.exponential_integrable μ z hz C hC t w

variable [Fintype A] [MeasurableSingletonClass A]

theorem phase_mean (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (w : ℂ) (t : ℝ≥0) :
    (∫ ω, phase z w t ω ∂probability μ) = Complex.exp ((t : ℂ)*symbol μ z w) :=
  MarkedRenewalExponentialTransform.process_transform μ z hz C hC t w

theorem transition_exponential (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (w : ℂ) (t : ℝ≥0) (x : ℂ) :
    MarkedRealizationMarkov.transition μ z t (fun y => Complex.exp (w*y)) x =
      Complex.exp (w*x)*Complex.exp ((t : ℂ)*symbol μ z w) := by
  change (∫ ω, Complex.exp (w*(x+value z t ω)) ∂probability μ) = _
  simp_rw [mul_add,Complex.exp_add]
  rw [integral_const_mul]
  exact congrArg (fun y => Complex.exp (w*x)*y) (phase_mean μ z hz C hC w t)

theorem phase_condExp (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (w : ℂ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (probability μ)[phase z w t | history z hz s] =ᵐ[probability μ]
      fun ω => phase z w s ω*Complex.exp (((t-s : ℝ≥0) : ℂ)*symbol μ z w) := by
  have he := MarkedRealizationMarkov.conditional_transition μ z hz s t hst
    (fun y => Complex.exp (w*y)) (by fun_prop) (phase_integrable μ z hz C hC w t)
  filter_upwards [he] with ω he
  change (probability μ)[phase z w t | history z hz s] ω =
    MarkedRealizationMarkov.transition μ z (t-s) (fun y => Complex.exp (w*y)) (value z s ω) at he
  rw [he,transition_exponential μ z hz C hC w (t-s)]
  rfl

def normalized (μ : Measure A) (z : A → ℂ) (w : ℂ) (t : ℝ≥0) (ω : Sample A) : ℂ :=
  Complex.exp (-(t : ℂ)*symbol μ z w)*phase z w t ω

theorem normalized_adapted (μ : Measure A) (z : A → ℂ) (hz : Measurable z) (w : ℂ) :
    StronglyAdapted (history z hz) (normalized μ z w) := fun t =>
  stronglyMeasurable_const.mul (phase_adapted z hz w t)

theorem normalized_integrable (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (w : ℂ) (t : ℝ≥0) :
    Integrable (normalized μ z w t) (probability μ) :=
  (phase_integrable μ z hz C hC w t).const_mul _

theorem normalized_condExp (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (w : ℂ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (probability μ)[normalized μ z w t | history z hz s] =ᵐ[probability μ] normalized μ z w s := by
  have he := condExp_smul (μ := probability μ) (Complex.exp (-(t : ℂ)*symbol μ z w))
    (phase z w t) (history z hz s)
  have hp := phase_condExp μ z hz C hC w s t hst
  have ht : ((t-s : ℝ≥0) : ℂ) = (t : ℂ)-(s : ℂ) := by
    rw [NNReal.coe_sub hst]
    push_cast
    rfl
  have hh : Complex.exp (-(t : ℂ)*symbol μ z w)*
      Complex.exp (((t-s : ℝ≥0) : ℂ)*symbol μ z w) = Complex.exp (-(s : ℂ)*symbol μ z w) := by
    rw [← Complex.exp_add,ht]
    congr 1
    ring
  filter_upwards [he,hp] with ω he hp
  change (probability μ)[normalized μ z w t | history z hz s] ω =
    Complex.exp (-(t : ℂ)*symbol μ z w)*(probability μ)[phase z w t | history z hz s] ω at he
  rw [he,hp]
  change _ = Complex.exp (-(s : ℂ)*symbol μ z w)*phase z w s ω
  calc
    _ = (Complex.exp (-(t : ℂ)*symbol μ z w)*
        Complex.exp (((t-s : ℝ≥0) : ℂ)*symbol μ z w))*phase z w s ω := by ring
    _ = _ := by rw [hh]

theorem normalized_martingale (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (w : ℂ) :
    Martingale (normalized μ z w) (history z hz) (probability μ) :=
  ⟨normalized_adapted μ z hz w,fun s t hst => normalized_condExp μ z hz C hC w s t hst⟩

theorem normalized_mean (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (w : ℂ) (t : ℝ≥0) :
    (∫ ω, normalized μ z w t ω ∂probability μ) = 1 := by
  change (∫ ω, Complex.exp (-(t : ℂ)*symbol μ z w)*phase z w t ω ∂probability μ) = _
  rw [integral_const_mul,phase_mean μ z hz C hC w t,← Complex.exp_add]
  have he : -(t : ℂ)*symbol μ z w+(t : ℂ)*symbol μ z w = 0 := by ring
  rw [he,Complex.exp_zero]

theorem normalized_zero (μ : Measure A) (z : A → ℂ) (w : ℂ) (ω : Sample A) :
    normalized μ z w 0 ω = 1 := by
  simp [normalized,phase,value,process_zero]

end OperatorDerivativeRewrite.Foundation.MarkedRealizationExponentialMartingale
