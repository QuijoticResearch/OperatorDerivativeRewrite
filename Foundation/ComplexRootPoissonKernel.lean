import Foundation.ComplexRootPoissonSemigroup
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Actual complex compound-root Markov kernels and their Chapman--Kolmogorov law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonKernel
open ComplexRootTransitionOperator ComplexRootPoissonSemigroup

theorem ext_complex {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : ℂ →ᵇ ℂ, (∫ z, f z ∂μ) = ∫ z, f z ∂ν) : μ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let F : ℂ →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup (fun z => ((f z : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp f.continuous) ‖f‖ (fun z => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using f.norm_coe_le_norm z)
  have he := h F
  change (∫ z, ((f z : ℝ) : ℂ) ∂μ) = ∫ z, ((f z : ℝ) : ℂ) ∂ν at he
  rw [integral_complex_ofReal, integral_complex_ofReal] at he
  exact Complex.ofReal_injective he

def kernel (a : ℝ) (r : ℝ≥0) : Kernel ℂ ℂ :=
  ((Kernel.id : Kernel ℂ ℂ) ×ₖ Kernel.const ℂ (ComplexRootPoissonLaw.law r a)).map
    (fun p : ℂ × ℂ => p.1+p.2)

instance kernel_isMarkov (a : ℝ) (r : ℝ≥0) : IsMarkovKernel (kernel a r) := by
  unfold kernel
  exact Kernel.IsMarkovKernel.map _ (measurable_fst.add measurable_snd)

theorem kernel_apply (a : ℝ) (r : ℝ≥0) (z : ℂ) :
    kernel a r z = (ComplexRootPoissonLaw.law r a).map (fun y => z+y) := by
  have hm : Measurable (fun p : ℂ × ℂ => p.1+p.2) := by fun_prop
  have hmk : Measurable (Prod.mk z : ℂ → ℂ × ℂ) := by fun_prop
  rw [kernel, Kernel.map_apply _ hm, Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map hm hmk]
  rfl

theorem kernel_integral (a : ℝ) (r : ℝ≥0) (f : Test) (z : ℂ) :
    (∫ y, f y ∂kernel a r z) = transition a r f z := by
  have hm : Measurable (fun y : ℂ => z+y) := by fun_prop
  rw [kernel_apply, integral_map hm.aemeasurable
    f.continuous.aestronglyMeasurable]
  exact (transition_law a r f z).symm

theorem kernel_zero (a : ℝ) : kernel a 0 = Kernel.id := by
  ext1 z
  apply ext_complex
  intro f
  rw [kernel_integral, Kernel.id_apply, integral_dirac, NNReal.coe_zero, transition_zero]
  rfl

theorem kernel_add (a : ℝ) (s t : ℝ≥0) :
    kernel a (s+t) = kernel a t ∘ₖ kernel a s := by
  ext1 z
  apply ext_complex
  intro f
  rw [kernel_integral, Kernel.integral_comp (f.integrable (μ := (kernel a t ∘ₖ kernel a s) z))]
  simp_rw [kernel_integral]
  simp only [NNReal.coe_add, transition_add, ContinuousLinearMap.comp_apply]

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonKernel
