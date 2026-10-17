import Foundation.GaussianMehler
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! The actual Mehler transition probabilities as a measurable Markov kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianMehlerKernel
open GaussianMehler

def affine (t x y : ℝ) : ℝ :=
  Real.exp (-t)*x+Real.sqrt (1-Real.exp (-2*t))*y

theorem affine_measurable (t x : ℝ) : Measurable (affine t x) := by unfold affine; fun_prop

theorem affine_joint_measurable (t : ℝ) :
    Measurable (fun p : ℝ × ℝ => affine t p.1 p.2) := by unfold affine; fun_prop

def kernel (t : ℝ) : Kernel ℝ ℝ where
  toFun x := γ.map (affine t x)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    simp_rw [Measure.map_apply (affine_measurable t _) hs]
    exact measurable_measure_prodMk_left (hs.preimage (affine_joint_measurable t))

theorem kernel_apply (t x : ℝ) : kernel t x = γ.map (affine t x) := rfl

instance kernel_markov (t : ℝ) : IsMarkovKernel (kernel t) := by
  constructor
  intro x
  constructor
  change γ.map (affine t x) Set.univ = 1
  rw [Measure.map_apply (affine_measurable t x) MeasurableSet.univ, Set.preimage_univ, measure_univ]

theorem integral_kernel (t x : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ y, f y ∂kernel t x) = mehler t f x := by
  rw [kernel_apply, integral_map (affine_measurable t x).aemeasurable hf.measurable.aestronglyMeasurable]
  rfl

theorem kernel_zero : kernel 0 = Kernel.id := by
  ext x : 1
  rw [kernel_apply]
  have he : affine 0 x = fun _ : ℝ => x := by funext y; simp [affine]
  rw [he, Measure.map_const]
  simp
  rfl

theorem kernel_compose (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    kernel (s+t) = kernel t ∘ₖ kernel s := by
  ext x : 1
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_kernel _ _ f.continuous,
    Kernel.integral_comp (BoundedContinuousFunction.integrable _ f)]
  simp_rw [integral_kernel t _ f.continuous]
  rw [integral_kernel s _ (mehler_continuous f.continuous f.norm_coe_le_norm t)]
  exact congrFun (mehler_compose s t hs ht f.continuous f.norm_coe_le_norm) x

theorem kernel_invariant (t : ℝ) (ht : 0 ≤ t) : kernel t ∘ₘ γ = γ := by
  rw [Measure.comp_eq_comp_const_apply]
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [Kernel.integral_comp (BoundedContinuousFunction.integrable _ f)]
  simp_rw [integral_kernel t _ f.continuous]
  exact integral_mehler f.continuous f.norm_coe_le_norm t ht

theorem time_continuous {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) (x : ℝ) :
    Continuous (fun t => ∫ y, f y ∂kernel t x) := by
  simp_rw [integral_kernel _ _ hf]
  rw [continuous_iff_continuousAt]
  intro t
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => M)
  · exact Eventually.of_forall fun s => (kernel_integrable hf hM s x).1
  · exact Eventually.of_forall fun s => Eventually.of_forall fun y => hM _
  · exact integrable_const M
  · apply Eventually.of_forall
    intro y
    apply hf.continuousAt.tendsto.comp
    apply Continuous.continuousAt
    fun_prop

end OperatorDerivativeRewrite.Foundation.GaussianMehlerKernel
