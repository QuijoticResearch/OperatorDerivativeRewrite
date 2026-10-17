import Foundation.GaussianInstantaneousProductProcess
import Mathlib.Probability.BorelCantelli

/-! Natural-past conditional laws for the actual instantaneous Gaussian process.
The Markov identity is proved for all bounded measurable real observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianInstantaneousMarkov
open GaussianMehler GaussianAcceleratedKernelLimit GaussianInstantaneousProductProcess

def history : Filtration ℝ (inferInstance : MeasurableSpace PathSpace) :=
  Filtration.natural process (fun t => (process_measurable t).stronglyMeasurable)

theorem process_adapted : StronglyAdapted history process :=
  Filtration.stronglyAdapted_natural (fun t => (process_measurable t).stronglyMeasurable)

theorem future_independent (x s t : ℝ) (hst : s < t) :
    Indep (MeasurableSpace.comap (process t) inferInstance) (history s) (pathMeasure x) :=
  (process_independent x).indep_comap_natural_of_lt
    (fun t => (process_measurable t).stronglyMeasurable) hst

theorem observable_integrable (x t : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) :
    Integrable (fun ω => f (process t ω)) (pathMeasure x) :=
  integrable_comp_of_bounded hf hM (process_measurable t)

theorem future_condExp (x s t : ℝ) (hs : 0 ≤ s) (hst : s < t)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (pathMeasure x)[fun ω => f (process t ω) | history s] =ᵐ[pathMeasure x]
      fun _ => ∫ y, f y ∂γ := by
  have hm : Measurable[MeasurableSpace.comap (process t) inferInstance]
      (fun ω => f (process t ω)) := hf.comp (comap_measurable (process t))
  have h := condExp_indep_eq (process_measurable t).comap_le (history.le s)
    hm.stronglyMeasurable (future_independent x s t hst)
  have hl : HasLaw (process t) γ (pathMeasure x) :=
    GaussianKernelPathObstruction.positive_row_law (pathMeasure x) process x
      (fun r _ => process_law x r) t (hs.trans_lt hst)
  have hi : (∫ ω, f (process t ω) ∂pathMeasure x) = ∫ y, f y ∂γ := by
    simpa only [Function.comp_def] using hl.integral_comp hf.aestronglyMeasurable
  simpa only [hi] using h

theorem markov_condExp (x s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (f : ℝ → ℝ) (hf : Measurable f) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) :
    (pathMeasure x)[fun ω => f (process t ω) | history s] =ᵐ[pathMeasure x]
      fun ω => ∫ y, f y ∂limitKernel (t-s) (process s ω) := by
  rcases eq_or_lt_of_le hst with he | hlt
  · subst t
    have hm : StronglyMeasurable[history s] (fun ω => f (process s ω)) :=
      (hf.comp (process_adapted s).measurable).stronglyMeasurable
    rw [condExp_of_stronglyMeasurable (history.le s) hm
      (observable_integrable x s f hf hM)]
    apply Filter.Eventually.of_forall
    intro ω
    simp [sub_self, limit_integral]
  · have h := future_condExp x s t hs hlt f hf
    apply h.trans
    apply Filter.Eventually.of_forall
    intro ω
    simp [limit_integral, ne_of_gt (sub_pos.mpr hlt)]

theorem boundedContinuous_markov (x s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (f : BoundedContinuousFunction ℝ ℝ) :
    (pathMeasure x)[fun ω => f (process t ω) | history s] =ᵐ[pathMeasure x]
      fun ω => ∫ y, f y ∂limitKernel (t-s) (process s ω) :=
  markov_condExp x s t hs hst f f.continuous.measurable f.norm_coe_le_norm

theorem indicator_markov (x s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (pathMeasure x)[fun ω => A.indicator (fun _ => (1 : ℝ)) (process t ω) | history s]
      =ᵐ[pathMeasure x] fun ω => (limitKernel (t-s) (process s ω)).real A := by
  have h := markov_condExp x s t hs hst (A.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hA) (M := 1) (by
      intro y
      by_cases hy : y ∈ A <;> simp [hy])
  apply h.trans
  apply Filter.Eventually.of_forall
  intro ω
  simp [integral_indicator_const (1 : ℝ) hA, measureReal_def]

end OperatorDerivativeRewrite.Foundation.GaussianInstantaneousMarkov
