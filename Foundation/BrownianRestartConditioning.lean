import Foundation.BrownianBoundedRestartProcess
import Foundation.IndependentPastConditioning

/-! The actual restarted continuous Brownian path is still Brownian after
conditioning on any positive-probability event in the original stopped past. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianRestartConditioning
open InfiniteGaussian BrownianMassClockStoppingTime BrownianStoppedFourier
open BrownianStoppedIncrementLaw BrownianBoundedRestartProcess
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

variable (τ : SampleSpace → ℝ≥0)
  (hτ : IsStoppingTime augmentedPast (fun ω => (τ ω : WithTop ℝ≥0)))

theorem stopped_le_shifted (t : ℝ≥0) : hτ.measurableSpace ≤ shiftedPast τ hτ t :=
  hτ.measurableSpace_mono (delay_isStoppingTime augmentedPast τ hτ t)
    (fun ω => WithTop.coe_le_coe.mpr (le_add_right le_rfl))

theorem coordinate_law_cond (N : ℕ) (hN : ∀ ω, τ ω ≤ N)
    (A : Set SampleSpace) (hA : MeasurableSet[hτ.measurableSpace] A)
    (hμA : gaussianProduct A ≠ 0) (t : ℝ≥0) :
    HasLaw (process τ t) (gaussianReal 0 t) gaussianProduct[|A] := by
  have hI : Indep (MeasurableSpace.comap (process τ t) inferInstance)
      hτ.measurableSpace gaussianProduct := by
    rw [process_eq_increment]
    exact increment_independent τ hτ t N hN
  have he := IndependentPastConditioning.map_law _ _ gaussianProduct (process τ t)
    (comap_measurable (process τ t)) (coordinate_measurable τ hτ t).comap_le hI A hA hμA
  exact ⟨(coordinate_measurable τ hτ t).aemeasurable,
    he.trans (coordinate_law τ hτ N hN t).map_eq⟩

theorem future_independent_cond (N : ℕ) (hN : ∀ ω, τ ω ≤ N)
    (A : Set SampleSpace) (hA : MeasurableSet[hτ.measurableSpace] A)
    (hμA : gaussianProduct A ≠ 0) (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => process τ t ω-process τ s ω) inferInstance)
      (shiftedPast τ hτ s) gaussianProduct[|A] :=
  IndependentPastConditioning.independence _ _ gaussianProduct
    ((coordinate_measurable τ hτ t).sub (coordinate_measurable τ hτ s)).comap_le
    ((shiftedPast τ hτ).le s) (future_difference_independent τ hτ N hN s t hst)
    A (stopped_le_shifted τ hτ s A hA) hμA

theorem independent_increments_cond (N : ℕ) (hN : ∀ ω, τ ω ≤ N)
    (A : Set SampleSpace) (hA : MeasurableSet[hτ.measurableSpace] A)
    (hμA : gaussianProduct A ≠ 0) :
    HasIndepIncrements (process τ) gaussianProduct[|A] := by
  letI : IsProbabilityMeasure gaussianProduct[|A] := cond_isProbabilityMeasure hμA
  exact SequentialIncrementIndependence.of_filtration gaussianProduct[|A]
    (shiftedPast τ hτ) (process τ) (adapted_coordinate τ hτ)
    (future_independent_cond τ hτ N hN A hA hμA)

theorem isBrownian_cond (N : ℕ) (hN : ∀ ω, τ ω ≤ N)
    (A : Set SampleSpace) (hA : MeasurableSet[hτ.measurableSpace] A)
    (hμA : gaussianProduct A ≠ 0) : IsBrownianReal (process τ) gaussianProduct[|A] := by
  letI : IsProbabilityMeasure gaussianProduct[|A] := cond_isProbabilityMeasure hμA
  exact ⟨HasIndepIncrements.isPreBrownianReal_of_hasLaw
    (coordinate_law_cond τ hτ N hN A hA hμA)
    (independent_increments_cond τ hτ N hN A hA hμA),
    Eventually.of_forall (fun ω => (path τ ω).continuous)⟩

end OperatorDerivativeRewrite.Foundation.BrownianRestartConditioning
