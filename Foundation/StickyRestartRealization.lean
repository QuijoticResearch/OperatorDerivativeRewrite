import Foundation.BrownianFiniteStrongMarkov
import Foundation.StickyWienerPathRealization

/-! Actual fresh sticky paths driven by Brownian innovations after a finite
stopping time. Their laws and independence are realized, without identifying
them with the physical-time continuation of the original sticky path. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyRestartRealization
open InfiniteGaussian BrownianMassClockStoppingTime BrownianBoundedRestartProcess
open StickyWienerPathRealization
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

def restartedSticky (κ : ℝ≥0) (τ : SampleSpace → ℝ≥0) (ω : SampleSpace) : C(ℝ≥0, ℝ) :=
  stickyPath κ (path τ ω)

variable (κ : ℝ≥0) (τ : SampleSpace → ℝ≥0)
  (hτ : IsStoppingTime augmentedPast (fun ω => (τ ω : WithTop ℝ≥0)))

include hτ in
theorem path_measurable : Measurable (restartedSticky κ τ) :=
  (stickyPath_measurable κ).comp (BrownianBoundedRestartProcess.path_measurable τ hτ)

include hτ in
theorem path_law : gaussianProduct.map (restartedSticky κ τ) =
    gaussianProduct.map (BrownianMassRandomTimeChange.changedPath κ) := by
  change gaussianProduct.map (stickyPath κ ∘ path τ) = _
  rw [← Measure.map_map (stickyPath_measurable κ)
    (BrownianBoundedRestartProcess.path_measurable τ hτ),
    BrownianFiniteStrongMarkov.path_law τ hτ]
  exact stickyPath_law κ

theorem path_independent :
    Indep (MeasurableSpace.comap (restartedSticky κ τ) inferInstance)
      hτ.measurableSpace gaussianProduct := by
  have hm : Measurable[MeasurableSpace.comap (path τ) inferInstance]
      (restartedSticky κ τ) := (stickyPath_measurable κ).comp (comap_measurable (path τ))
  exact indep_of_indep_of_le_left (BrownianFiniteStrongMarkov.path_independent τ hτ) hm.comap_le

theorem observable_projection (f : C(ℝ≥0, ℝ) → ℝ) (hf : Measurable f)
    (hi : Integrable f (gaussianProduct.map (BrownianMassRandomTimeChange.changedPath κ))) :
    Integrable (fun ω => f (restartedSticky κ τ ω)) gaussianProduct ∧
      gaussianProduct[(fun ω => f (restartedSticky κ τ ω)) | hτ.measurableSpace]
        =ᵐ[gaussianProduct]
      (fun _ => ∫ p, f p ∂gaussianProduct.map (BrownianMassRandomTimeChange.changedPath κ)) := by
  have hl : HasLaw (restartedSticky κ τ)
      (gaussianProduct.map (BrownianMassRandomTimeChange.changedPath κ)) gaussianProduct :=
    ⟨(path_measurable κ τ hτ).aemeasurable,path_law κ τ hτ⟩
  refine ⟨hl.integrable_comp hi,?_⟩
  have hm : Measurable[MeasurableSpace.comap (restartedSticky κ τ) inferInstance]
      (fun ω => f (restartedSticky κ τ ω)) := hf.comp (comap_measurable _)
  have hI := indep_of_indep_of_le_left (path_independent κ τ hτ) hm.comap_le
  have he := condExp_indep_eq (hf.comp (path_measurable κ τ hτ)).comap_le
    hτ.measurableSpace_le (comap_measurable _).stronglyMeasurable hI
  have hint : (∫ ω, f (restartedSticky κ τ ω) ∂gaussianProduct) =
      ∫ p, f p ∂gaussianProduct.map (BrownianMassRandomTimeChange.changedPath κ) :=
    hl.integral_comp hf.stronglyMeasurable.aestronglyMeasurable
  simpa only [Function.comp_def,hint] using he

theorem inverse_clock_independent_observed (η s : ℝ≥0) :
    Indep (MeasurableSpace.comap
      (restartedSticky κ (fun ω => BrownianMassRandomTimeChange.inverse η ω s)) inferInstance)
      (StickyNaturalClock.augmentedNaturalPast η s) gaussianProduct := by
  have hi := path_independent κ (fun ω => BrownianMassRandomTimeChange.inverse η ω s)
    (inverse_isStoppingTime η s)
  have hm := path_measurable κ (fun ω => BrownianMassRandomTimeChange.inverse η ω s)
    (inverse_isStoppingTime η s)
  have ha := AmbientIndependenceAugmentation.augment_right _ _ gaussianProduct hm.comap_le hi
  exact indep_of_indep_of_le_right ha (StickyNaturalMartingales.augmented_le_physical η s)

end OperatorDerivativeRewrite.Foundation.StickyRestartRealization
