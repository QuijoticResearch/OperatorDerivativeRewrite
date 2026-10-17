import Foundation.BrownianStoppedIncrementLaw
import Foundation.AmbientIndependenceAugmentation
import Foundation.StickyNaturalMartingales
import Mathlib.Probability.HasLaw
import Mathlib.Probability.ConditionalExpectation

/-! Actual Gaussian Brownian increments after the endogenous sticky clock,
independent of the observed sticky past. This is an operational-time increment,
not a deterministic physical-time increment of the sticky trajectory. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyOperationalFutureIncrement
open InfiniteGaussian IBMConstructedSources BrownianMassRandomTimeChange
open BrownianMassClockStoppingTime BrownianTimeChangedMartingales
open StickyNaturalClock StickyNaturalMartingales BrownianStoppedIncrementLaw
open AmbientNullAugmentation AmbientIndependenceAugmentation
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath
  BrownianMassRandomTimeChange.inverse BrownianRandomMassClock.mass

def futureIncrement (κ s h : ℝ≥0) (ω : SampleSpace) : ℝ :=
  clockPath ω (inverse κ ω s+h)-changedPath κ ω s

theorem futureIncrement_eq (κ s h : ℝ≥0) : futureIncrement κ s h =
    BrownianStoppedIncrementFourier.increment (fun ω => inverse κ ω s) h := rfl

theorem futureIncrement_measurable (κ s h : ℝ≥0) : Measurable (futureIncrement κ s h) := by
  rw [futureIncrement_eq]
  exact BrownianStoppedIncrementFourier.increment_measurable _ (inverse_isStoppingTime κ s) h

theorem futureIncrement_law (κ s h : ℝ≥0) :
    gaussianProduct.map (futureIncrement κ s h) = gaussianReal 0 h := by
  rw [futureIncrement_eq]
  exact increment_law _ (inverse_isStoppingTime κ s) h (Nat.ceil s)
    (fun ω => (inverse_le κ ω s).trans (Nat.le_ceil s))

theorem futureIncrement_hasLaw (κ s h : ℝ≥0) :
    HasLaw (futureIncrement κ s h) (gaussianReal 0 h) gaussianProduct :=
  ⟨(futureIncrement_measurable κ s h).aemeasurable,futureIncrement_law κ s h⟩

theorem independent_physical (κ s h : ℝ≥0) :
    Indep (MeasurableSpace.comap (futureIncrement κ s h) inferInstance)
      (physicalPast κ s) gaussianProduct := by
  rw [futureIncrement_eq]
  exact increment_independent _ (inverse_isStoppingTime κ s) h (Nat.ceil s)
    (fun ω => (inverse_le κ ω s).trans (Nat.le_ceil s))

theorem independent_augmented_physical (κ s h : ℝ≥0) :
    Indep (MeasurableSpace.comap (futureIncrement κ s h) inferInstance)
      (augment (physicalPast κ s) gaussianProduct) gaussianProduct :=
  augment_right _ _ gaussianProduct (futureIncrement_measurable κ s h).comap_le
    (independent_physical κ s h)

theorem independent_observed (κ s h : ℝ≥0) :
    Indep (MeasurableSpace.comap (futureIncrement κ s h) inferInstance)
      (augmentedNaturalPast κ s) gaussianProduct :=
  smaller_right _ _ gaussianProduct _ (augmented_le_physical κ s)
    (independent_augmented_physical κ s h)

theorem observation_realization (κ s h : ℝ≥0) (f : ℝ → ℝ) (hf : Measurable f)
    (hi : Integrable f (gaussianReal 0 h)) :
    Integrable (fun ω => f (futureIncrement κ s h ω)) gaussianProduct ∧
      gaussianProduct[(fun ω => f (futureIncrement κ s h ω)) | augmentedNaturalPast κ s]
        =ᵐ[gaussianProduct] (fun _ => ∫ x, f x ∂gaussianReal 0 h) := by
  have hl := futureIncrement_hasLaw κ s h
  refine ⟨hl.integrable_comp hi,?_⟩
  have hm : Measurable[MeasurableSpace.comap (futureIncrement κ s h) inferInstance]
      (fun ω => f (futureIncrement κ s h ω)) :=
    hf.comp (comap_measurable (futureIncrement κ s h))
  have hI : Indep (MeasurableSpace.comap (fun ω => f (futureIncrement κ s h ω)) inferInstance)
      (augmentedNaturalPast κ s) gaussianProduct :=
    (smaller_right _ _ gaussianProduct _ hm.comap_le (independent_observed κ s h).symm).symm
  have he := condExp_indep_eq (hf.comp (futureIncrement_measurable κ s h)).comap_le
    ((augmentedNaturalPast κ).le s)
    (comap_measurable (fun ω => f (futureIncrement κ s h ω))).stronglyMeasurable hI
  have hint : (∫ ω, f (futureIncrement κ s h ω) ∂gaussianProduct) =
      ∫ x, f x ∂gaussianReal 0 h :=
    hl.integral_comp hf.stronglyMeasurable.aestronglyMeasurable
  simpa only [hint] using he

end OperatorDerivativeRewrite.Foundation.StickyOperationalFutureIncrement
