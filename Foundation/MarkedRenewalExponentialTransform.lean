import Foundation.FiniteMarkedRenewalMarginals
import Foundation.PoissonEntireMoments

/-! Actual exponential transforms on bounded-mark renewal probability realizations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedRenewalExponentialTransform
open MarkedRenewalRealization FiniteMarkedRenewalMarginals
variable {A : Type*} [MeasurableSpace A]

theorem count_geometric_integrable (μ : Measure A) [IsProbabilityMeasure μ] (t : ℝ≥0) (B : ℝ) :
    Integrable (fun ω : Sample A => B^(ExponentialRenewalCount.count t ω.1)) (probability μ) := by
  have hi := (RenewalCompensatedMartingale.count_preserving t).integrable_comp_of_integrable
    (PoissonEntireMoments.real_powers_integrable t B)
  exact (show MeasurePreserving (Prod.fst : Sample A → ExponentialHoldingSequence.Sample)
    (probability μ) ExponentialHoldingSequence.probability from measurePreserving_fst).integrable_comp_of_integrable hi

theorem exponential_integrable (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ k, ‖z k‖ ≤ C) (t : ℝ≥0) (w : ℂ) :
    Integrable (fun ω => Complex.exp (w*process z t ω)) (probability μ) := by
  have hm : Measurable (fun ω => Complex.exp (w*process z t ω)) :=
    Complex.continuous_exp.measurable.comp (measurable_const.mul (process_measurable z hz t))
  apply (count_geometric_integrable μ t (Real.exp (‖w‖*C))).mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro ω
  calc
    _ ≤ Real.exp ‖w*process z t ω‖ := Complex.norm_exp_le_exp_norm _
    _ ≤ Real.exp (‖w‖*((ExponentialRenewalCount.count t ω.1 : ℝ)*C)) := by
      apply Real.exp_le_exp.mpr
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (position_norm_bound z C hC (ExponentialRenewalCount.count t ω.1) ω.2) (norm_nonneg w)
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

def oneStep (μ : Measure A) (z : A → ℂ) (w : ℂ) : ℂ := ∫ k, Complex.exp (w*z k) ∂μ

variable [Fintype A] [MeasurableSingletonClass A]

theorem finite_transform (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ) (n : ℕ) (w x : ℂ) :
    (∫ ξ, Complex.exp (w*(x+terminal z n ξ)) ∂finiteProbability μ n) =
      Complex.exp (w*x)*(oneStep μ z w)^n := by
  induction n generalizing x with
  | zero => simp [terminal]
  | succ n ih =>
    rw [terminal_successor μ z n (fun y : ℂ => Complex.exp (w*y)) x]
    simp_rw [ih]
    rw [integral_mul_const]
    have he (k : A) : Complex.exp (w*(x+z k)) = Complex.exp (w*x)*Complex.exp (w*z k) := by
      rw [mul_add,Complex.exp_add]
    simp_rw [he]
    rw [integral_const_mul]
    change Complex.exp (w*x)*oneStep μ z w*oneStep μ z w^n = _
    ring

theorem process_transform (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ k, ‖z k‖ ≤ C) (t : ℝ≥0) (w : ℂ) :
    (∫ ω, Complex.exp (w*process z t ω) ∂probability μ) =
      Complex.exp ((t : ℂ)*(oneStep μ z w-1)) := by
  rw [process_mixture μ z t (fun y : ℂ => Complex.exp (w*y)) (exponential_integrable μ z hz C hC t w)]
  have he (n : ℕ) : (∫ ξ, Complex.exp (w*terminal z n ξ) ∂finiteProbability μ n) = oneStep μ z w^n := by
    simpa only [zero_add,mul_zero,Complex.exp_zero,one_mul] using finite_transform μ z n w 0
  simp_rw [he]
  exact PoissonEntireMoments.complex_powers_integral t (oneStep μ z w)

end OperatorDerivativeRewrite.Foundation.MarkedRenewalExponentialTransform
