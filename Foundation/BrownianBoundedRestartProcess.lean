import Foundation.BrownianStoppedIncrementLaw
import Foundation.SequentialIncrementIndependence
import Foundation.StickyOperationalFutureIncrement

/-! A genuine Brownian process after an actual bounded stopping time. Its
continuous paths, measurable path realization and joint independent increments
are proved. Whole-path independence from the original stopped past is separate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianBoundedRestartProcess
open InfiniteGaussian IBMConstructedSources BrownianMassClockStoppingTime
open BrownianStoppedFourier BrownianStoppedIncrementLaw
open BrownianMassRandomTimeChange
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath
  BrownianMassRandomTimeChange.inverse BrownianRandomMassClock.mass

def path (τ : SampleSpace → ℝ≥0) (ω : SampleSpace) : C(ℝ≥0, ℝ) where
  toFun := fun t => clockPath ω (τ ω+t)-clockPath ω (τ ω)
  continuous_toFun := ((clockPath ω).continuous.comp
    (continuous_const.add continuous_id)).sub continuous_const

def process (τ : SampleSpace → ℝ≥0) (t : ℝ≥0) (ω : SampleSpace) : ℝ := path τ ω t

theorem process_eq_increment (τ : SampleSpace → ℝ≥0) (t : ℝ≥0) :
    process τ t = BrownianStoppedIncrementFourier.increment τ t := rfl

variable (τ : SampleSpace → ℝ≥0)
  (hτ : IsStoppingTime augmentedPast (fun ω => (τ ω : WithTop ℝ≥0)))

include hτ in
theorem coordinate_measurable (t : ℝ≥0) : Measurable (process τ t) := by
  rw [process_eq_increment]
  exact BrownianStoppedIncrementFourier.increment_measurable τ hτ t

include hτ in
theorem path_measurable : Measurable (path τ) :=
  ContinuousMap.measurable_iff_eval.mpr (coordinate_measurable τ hτ)

include hτ in
theorem process_joint : Measurable (fun z : ℝ≥0 × SampleSpace => process τ z.1 z.2) :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => (path τ ω).continuous)
    (coordinate_measurable τ hτ)

def shiftedPast : Filtration ℝ≥0 (inferInstance : MeasurableSpace SampleSpace) where
  seq t := (delay_isStoppingTime augmentedPast τ hτ t).measurableSpace
  mono' s t hst := (delay_isStoppingTime augmentedPast τ hτ s).measurableSpace_mono
    (delay_isStoppingTime augmentedPast τ hτ t)
    (fun ω => WithTop.coe_le_coe.mpr (add_le_add (le_refl (τ ω)) hst))
  le' t := (delay_isStoppingTime augmentedPast τ hτ t).measurableSpace_le

theorem adapted_coordinate (t : ℝ≥0) : Measurable[shiftedPast τ hτ t] (process τ t) := by
  have ht := brownian_at_stop_measurable (fun ω => τ ω+t)
    (delay_isStoppingTime augmentedPast τ hτ t)
  have h0 := (brownian_at_stop_measurable τ hτ).mono
    (hτ.measurableSpace_mono (delay_isStoppingTime augmentedPast τ hτ t)
      (fun ω => WithTop.coe_le_coe.mpr (le_add_right le_rfl))) le_rfl
  exact ht.sub h0

theorem difference_eq (s t : ℝ≥0) (hst : s ≤ t) :
    (fun ω => process τ t ω-process τ s ω) =
      BrownianStoppedIncrementFourier.increment (fun ω => τ ω+s) (t-s) := by
  funext ω
  dsimp [process,path,BrownianStoppedIncrementFourier.increment]
  rw [add_assoc,add_tsub_cancel_of_le hst]
  ring

theorem future_difference_independent (N : ℕ) (hN : ∀ ω, τ ω ≤ N)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => process τ t ω-process τ s ω) inferInstance)
      (shiftedPast τ hτ s) gaussianProduct := by
  rw [difference_eq τ s t hst]
  exact increment_independent (fun ω => τ ω+s) (delay_isStoppingTime _ _ hτ s) (t-s)
    (Nat.ceil ((N : ℝ≥0)+s))
    (fun ω => (add_le_add (hN ω) (le_refl s)).trans (Nat.le_ceil _))

include hτ in
theorem independent_increments (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    HasIndepIncrements (process τ) gaussianProduct :=
  SequentialIncrementIndependence.of_filtration gaussianProduct (shiftedPast τ hτ)
    (process τ) (adapted_coordinate τ hτ) (future_difference_independent τ hτ N hN)

include hτ in
theorem coordinate_law (N : ℕ) (hN : ∀ ω, τ ω ≤ N) (t : ℝ≥0) :
    HasLaw (process τ t) (gaussianReal 0 t) gaussianProduct := by
  refine ⟨(coordinate_measurable τ hτ t).aemeasurable,?_⟩
  rw [process_eq_increment]
  exact increment_law τ hτ t N hN

include hτ in
theorem isBrownian (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    IsBrownianReal (process τ) gaussianProduct :=
  ⟨HasIndepIncrements.isPreBrownianReal_of_hasLaw (coordinate_law τ hτ N hN)
    (independent_increments τ hτ N hN),Eventually.of_forall (fun ω => (path τ ω).continuous)⟩

theorem inverse_clock_isBrownian (κ s : ℝ≥0) :
    IsBrownianReal (process (fun ω => inverse κ ω s)) gaussianProduct :=
  isBrownian _ (inverse_isStoppingTime κ s) (Nat.ceil s)
    (fun ω => (inverse_le κ ω s).trans (Nat.le_ceil s))

end OperatorDerivativeRewrite.Foundation.BrownianBoundedRestartProcess
