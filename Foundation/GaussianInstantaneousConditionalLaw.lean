import Foundation.GaussianInstantaneousMarkov
import Mathlib.Probability.HasCondDistrib

/-! An explicit regular conditional distribution given the entire real-indexed
past, proved directly by joint-law factorization on the actual product space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace OperatorDerivativeRewrite.Foundation.GaussianInstantaneousConditionalLaw
open GaussianMehler GaussianAcceleratedKernelLimit GaussianInstantaneousProductProcess
open GaussianInstantaneousMarkov

def past (s : ℝ) (ω : PathSpace) : Iic s → ℝ := fun r => process r ω

theorem past_measurable (s : ℝ) : Measurable (past s) := by
  apply measurable_pi_lambda
  intro r
  exact process_measurable r

theorem history_eq_comap (s : ℝ) :
    history s = MeasurableSpace.comap (past s) inferInstance := by
  rw [history, Filtration.natural_eq_comap]
  rfl

theorem future_past_independent (x s t : ℝ) (hst : s < t) :
    IndepFun (process t) (past s) (pathMeasure x) := by
  change Indep (MeasurableSpace.comap (process t) inferInstance)
    (MeasurableSpace.comap (past s) inferInstance) (pathMeasure x)
  rw [← history_eq_comap]
  exact future_independent x s t hst

def conditionalKernel (s t : ℝ) : Kernel (Iic s → ℝ) ℝ :=
  (limitKernel (t-s)).comap (fun p : Iic s → ℝ => p ⟨s, by simp⟩)
    (measurable_pi_apply (⟨s, by simp⟩ : Iic s))

theorem conditionalKernel_positive (s t : ℝ) (hst : s < t) :
    conditionalKernel s t = Kernel.const (Iic s → ℝ) γ := by
  ext p A hA
  simp [conditionalKernel, Kernel.comap_apply, limit_positive (t-s) (sub_pos.mpr hst)]

theorem conditional_distribution (x s t : ℝ) (hs : 0 ≤ s) (hst : s < t) :
    HasCondDistrib (process t) (past s) (conditionalKernel s t) (pathMeasure x) := by
  rw [conditionalKernel_positive s t hst]
  change HasLaw (fun ω => (past s ω, process t ω))
    (((pathMeasure x).map (past s)) ⊗ₘ Kernel.const (Iic s → ℝ) γ) (pathMeasure x)
  refine ⟨((past_measurable s).prodMk (process_measurable t)).aemeasurable, ?_⟩
  rw [Measure.compProd_const]
  rw [(future_past_independent x s t hst).symm.map_prod_eq_prod_map_map
    (past_measurable s).aemeasurable (process_measurable t).aemeasurable]
  have hl : HasLaw (process t) γ (pathMeasure x) :=
    GaussianKernelPathObstruction.positive_row_law (pathMeasure x) process x
      (fun r _ => process_law x r) t (hs.trans_lt hst)
  rw [hl.map_eq]

end OperatorDerivativeRewrite.Foundation.GaussianInstantaneousConditionalLaw
