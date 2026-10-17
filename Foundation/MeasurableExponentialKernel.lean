import Foundation.BoundedExponentialTiltResponse
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.WithDensity

/-! Actual normalized exponential probability kernels from jointly measurable exponents. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace OperatorDerivativeRewrite.Foundation.MeasurableExponentialKernel
variable {P E : Type*} [MeasurableSpace P] [MeasurableSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ] (X : P → E → ℝ)

def partition (p : P) : ℝ := ∫ x, Real.exp (X p x) ∂μ

def density (p : P) (x : E) : ℝ := Real.exp (X p x) / partition μ X p

theorem partition_measurable (hX : Measurable (Function.uncurry X)) :
    Measurable (partition μ X) :=
  hX.exp.stronglyMeasurable.integral_prod_right.measurable

theorem density_measurable (hX : Measurable (Function.uncurry X)) :
    Measurable (Function.uncurry (density μ X)) :=
  hX.exp.div ((partition_measurable μ X hX).comp measurable_fst)

omit [MeasurableSpace P] in
theorem partition_positive (p : P) (hI : Integrable (fun x => Real.exp (X p x)) μ) :
    0 < partition μ X p := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos (X p x)).le) hI).mpr
  have hs : Function.support (fun x => Real.exp (X p x)) = univ := by
    ext x
    simp [Function.mem_support, Real.exp_ne_zero]
  rw [hs]
  simp

omit [MeasurableSpace P] in
theorem density_integral (p : P) (hI : Integrable (fun x => Real.exp (X p x)) μ) :
    (∫ x, density μ X p x ∂μ) = 1 := by
  change (∫ x, Real.exp (X p x) / partition μ X p ∂μ) = 1
  rw [integral_div]
  exact div_self (partition_positive μ X p hI).ne'

def kernel : Kernel P E :=
  (Kernel.const P μ).withDensity (fun p x => ENNReal.ofReal (density μ X p x))

theorem kernel_apply (hX : Measurable (Function.uncurry X)) (p : P) :
    kernel μ X p = μ.withDensity (fun x => ENNReal.ofReal (density μ X p x)) := by
  rw [kernel, Kernel.withDensity_apply _ (density_measurable μ X hX).ennreal_ofReal]
  rfl

theorem kernel_probability (hX : Measurable (Function.uncurry X))
    (hI : ∀ p, Integrable (fun x => Real.exp (X p x)) μ) (p : P) :
    IsProbabilityMeasure (kernel μ X p) := by
  constructor
  rw [kernel_apply μ X hX, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hi : Integrable (density μ X p) μ := (hI p).div_const _
  have hn : ∀ x, 0 ≤ density μ X p x := fun x =>
    (div_pos (Real.exp_pos _) (partition_positive μ X p (hI p))).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn),
    density_integral μ X p (hI p)]
  norm_num

theorem kernel_markov (hX : Measurable (Function.uncurry X))
    (hI : ∀ p, Integrable (fun x => Real.exp (X p x)) μ) : IsMarkovKernel (kernel μ X) :=
  ⟨kernel_probability μ X hX hI⟩

end OperatorDerivativeRewrite.Foundation.MeasurableExponentialKernel
