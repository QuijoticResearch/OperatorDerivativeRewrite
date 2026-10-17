import Foundation.StickyObservedClock
import Foundation.AmbientNullAugmentation
import Foundation.BrownianAugmentedMartingales

/-! The full observed sticky trajectory retains the original Brownian path,
up to ambient null augmentation. This is not a filtration or Markov theorem. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyBrownianRecovery
open InfiniteGaussian IBMConstructedSources BrownianMassRandomTimeChange
open BrownianRandomMassClock StickyObservedClock
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath
  BrownianMassRandomTimeChange.inverse BrownianRandomMassClock.mass

@[instance_reducible] def observedSpace (κ : ℝ≥0) : MeasurableSpace SampleSpace :=
  MeasurableSpace.comap (changedPath κ) inferInstance

theorem observedSpace_le (κ : ℝ≥0) :
    observedSpace κ ≤ (inferInstance : MeasurableSpace SampleSpace) :=
  (changedPath_measurable κ).comap_le

@[instance_reducible] def observedAug (κ : ℝ≥0) : MeasurableSpace SampleSpace :=
  AmbientNullAugmentation.augment (observedSpace κ) gaussianProduct

theorem changedPath_observed (κ : ℝ≥0) : Measurable[observedAug κ] (changedPath κ) :=
  (comap_measurable (changedPath κ)).mono
    (AmbientNullAugmentation.raw_le (observedSpace κ) gaussianProduct (observedSpace_le κ)) le_rfl

theorem inverse_observed (κ T : ℝ≥0) :
    Measurable[observedAug κ] (fun ω => inverse κ ω T) := by
  have hr : Measurable[observedSpace κ]
      (fun ω => inverseFromPath (changedPath κ ω) T) :=
    inverseFromPath_joint.comp ((comap_measurable (changedPath κ)).prodMk measurable_const)
  apply AmbientNullAugmentation.measurable_of_raw_aestronglyMeasurable
    (observedSpace κ) gaussianProduct (inverse_coordinate_measurable κ T)
  exact hr.stronglyMeasurable.aestronglyMeasurable.congr
    (inverse_recovery.mono (fun _ h => h κ T))

theorem forward_lt_iff (κ s b : ℝ≥0) (ω : SampleSpace) :
    forward κ ω s < b ↔ s < inverse κ ω b := by
  simpa only [forward_inverse] using
    (forward_strictMono κ ω).lt_iff_lt (a := s) (b := inverse κ ω b)

theorem forward_observed (κ s : ℝ≥0) :
    Measurable[observedAug κ] (fun ω => forward κ ω s) := by
  apply measurable_of_Iio
  intro b
  have he : {ω | forward κ ω s < b} = {ω | s < inverse κ ω b} := by
    ext ω
    exact forward_lt_iff κ s b ω
  change MeasurableSet[observedAug κ] {ω | forward κ ω s < b}
  rw [he]
  exact measurableSet_lt measurable_const (inverse_observed κ b)

theorem brownian_coordinate_observed (κ s : ℝ≥0) :
    Measurable[observedAug κ] (fun ω => clockPath ω s) := by
  have hm : Measurable[observedAug κ]
      (fun ω => changedPath κ ω (forward κ ω s)) :=
    continuous_eval.measurable.comp ((changedPath_observed κ).prodMk (forward_observed κ s))
  simpa only [recover_original] using hm

theorem brownian_path_observed (κ : ℝ≥0) : Measurable[observedAug κ] clockPath := by
  letI : MeasurableSpace SampleSpace := observedAug κ
  exact ContinuousMap.measurable_iff_eval.mpr (brownian_coordinate_observed κ)

theorem brownian_space_le (κ : ℝ≥0) :
    MeasurableSpace.comap clockPath inferInstance ≤ observedAug κ :=
  (brownian_path_observed κ).comap_le

theorem brownian_condExp_observed (κ s : ℝ≥0) :
    gaussianProduct[fun ω => clockPath ω s | observedSpace κ] =ᵐ[gaussianProduct]
      (fun ω => clockPath ω s) := by
  have hi := BrownianAugmentedMartingales.brownian_integrable s
  have he := AmbientNullAugmentation.condExp_invariant (observedSpace κ) gaussianProduct
    (observedSpace_le κ) (fun ω => clockPath ω s) hi
  rw [condExp_of_stronglyMeasurable
    (AmbientNullAugmentation.le_ambient (observedSpace κ) gaussianProduct)
    (brownian_coordinate_observed κ s).stronglyMeasurable hi] at he
  exact he

end OperatorDerivativeRewrite.Foundation.StickyBrownianRecovery
