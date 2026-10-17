import Foundation.BrownianFiniteStrongMarkov

/-! Almost surely finite WithTop stopping times admit everywhere finite
versions for the actual augmented Brownian filtration, with the same stopped
sigma-algebra. This extends the verified whole-path restart theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianAlmostSureStrongMarkov
open InfiniteGaussian GaussianTimeProcess BrownianMassClockStoppingTime
open BrownianBoundedRestartProcess
set_option backward.isDefEq.respectTransparency false

def finiteVersion (τ : SampleSpace → WithTop ℝ≥0) (ω : SampleSpace) : ℝ≥0 :=
  (τ ω).untopD 0

theorem finiteVersion_le (τ : SampleSpace → WithTop ℝ≥0) (ω : SampleSpace) :
    (finiteVersion τ ω : WithTop ℝ≥0) ≤ τ ω := by
  cases h : τ ω with
  | top => exact le_top
  | coe a =>
    unfold finiteVersion
    rw [h]
    exact le_rfl

theorem event_eq (τ : SampleSpace → WithTop ℝ≥0) (t : ℝ≥0) :
    {ω | (finiteVersion τ ω : WithTop ℝ≥0) ≤ t} =
      {ω | τ ω ≤ t} ∪ {ω | τ ω = ⊤} := by
  ext ω
  cases h : τ ω with
  | top => simp [finiteVersion,h,WithTop.untopD_coe]
  | coe a =>
    change (finiteVersion τ ω : WithTop ℝ≥0) ≤ t ↔ τ ω ≤ t ∨ τ ω = ⊤
    unfold finiteVersion
    rw [h]
    change (a : WithTop ℝ≥0) ≤ t ↔ (a : WithTop ℝ≥0) ≤ t ∨ (a : WithTop ℝ≥0) = ⊤
    constructor
    · exact Or.inl
    · rintro (ha | ha)
      · exact ha
      · cases ha

variable (τ : SampleSpace → WithTop ℝ≥0) (hτ : IsStoppingTime augmentedPast τ)
  (hf : ∀ᵐ ω ∂gaussianProduct, τ ω ≠ ⊤)

include hτ hf

theorem exceptional_null : gaussianProduct {ω | τ ω = ⊤} = 0 := by
  simpa only [not_not] using ae_iff.mp hf

theorem finiteVersion_stopping :
    IsStoppingTime augmentedPast (fun ω => (finiteVersion τ ω : WithTop ℝ≥0)) := by
  intro t
  rw [event_eq]
  exact (hτ t).union (AmbientNullAugmentation.measurableSet_null
    (naturalFiltration t) gaussianProduct _ hτ.measurableSet_eq_top
      (exceptional_null τ hτ hf))

theorem stopped_past_le : hτ.measurableSpace ≤
    (finiteVersion_stopping τ hτ hf).measurableSpace := by
  intro A hA
  refine ⟨hA.1,fun t => ?_⟩
  rw [event_eq,Set.inter_union_distrib_left]
  apply (hA.2 t).union
  exact AmbientNullAugmentation.measurableSet_null (naturalFiltration t) gaussianProduct _
    ((hτ.measurableSpace_le A hA).inter hτ.measurableSet_eq_top)
    (measure_mono_null inter_subset_right (exceptional_null τ hτ hf))

theorem stopped_past_eq : (finiteVersion_stopping τ hτ hf).measurableSpace =
    hτ.measurableSpace :=
  le_antisymm ((finiteVersion_stopping τ hτ hf).measurableSpace_mono hτ
    (finiteVersion_le τ)) (stopped_past_le τ hτ hf)

include hτ hf in
theorem path_law : gaussianProduct.map (path (finiteVersion τ)) =
    gaussianProduct.map IBMConstructedSources.clockPath :=
  BrownianFiniteStrongMarkov.path_law _ (finiteVersion_stopping τ hτ hf)

theorem path_independent :
    Indep (MeasurableSpace.comap (path (finiteVersion τ)) inferInstance)
      hτ.measurableSpace gaussianProduct := by
  rw [← stopped_past_eq τ hτ hf]
  exact BrownianFiniteStrongMarkov.path_independent _ (finiteVersion_stopping τ hτ hf)

end OperatorDerivativeRewrite.Foundation.BrownianAlmostSureStrongMarkov
