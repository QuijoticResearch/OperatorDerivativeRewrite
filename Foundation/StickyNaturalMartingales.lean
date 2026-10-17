import Foundation.StickyNaturalClock
import Foundation.BrownianTimeChangedVariance
import Foundation.AmbientMartingaleModification

/-! The actual sticky candidate and its compensated square are martingales
in the observed process's own filtration, not only a larger stopping filtration. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyNaturalMartingales
open InfiniteGaussian BrownianMassRandomTimeChange BrownianTimeChangedMartingales
open BrownianTimeChangedVariance StickyNaturalClock AmbientNullAugmentation
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath
  BrownianMassRandomTimeChange.inverse BrownianRandomMassClock.mass

theorem shrink {Ω ι : Type*} [m : MeasurableSpace Ω] [Preorder ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ 𝓖 : Filtration ι m)
    (hle : ∀ t, ℱ t ≤ 𝓖 t) (M : ι → Ω → ℝ)
    (hM : Martingale M 𝓖 μ) (ha : StronglyAdapted ℱ M) : Martingale M ℱ μ := by
  refine ⟨ha,?_⟩
  intro s t hst
  calc
    μ[M t | ℱ s] =ᵐ[μ] μ[μ[M t | 𝓖 s] | ℱ s] :=
      (condExp_condExp_of_le (hle s) (𝓖.le s)).symm
    _ =ᵐ[μ] μ[M s | ℱ s] := condExp_congr_ae (hM.condExp_ae_eq hst)
    _ =ᵐ[μ] M s := Eventually.of_forall (fun ω => congrFun
      (condExp_of_stronglyMeasurable (ℱ.le s) (ha s) (hM.integrable s)) ω)

theorem natural_le_physical (κ t : ℝ≥0) : naturalPast κ t ≤ physicalPast κ t := by
  change (⨆ s ≤ t, MeasurableSpace.comap (fun ω => changedPath κ ω s) inferInstance) ≤ _
  refine iSup₂_le (fun s hst => ?_)
  exact ((changed_brownian_martingale κ).stronglyAdapted s).measurable.comap_le.trans
    ((physicalPast κ).mono hst)

theorem augmented_le_physical (κ t : ℝ≥0) :
    augmentedNaturalPast κ t ≤ filtration gaussianProduct (physicalPast κ) t :=
  AmbientNullAugmentation.monotone gaussianProduct (natural_le_physical κ t)

theorem state_augmented_adapted (κ : ℝ≥0) :
    StronglyAdapted (augmentedNaturalPast κ) (fun t ω => changedPath κ ω t) :=
  fun t => (state_stronglyAdapted κ t).mono
    (filtration_raw_le gaussianProduct (naturalPast κ) t)

theorem natural_martingale (κ : ℝ≥0) :
    Martingale (fun t ω => changedPath κ ω t) (naturalPast κ) gaussianProduct :=
  shrink gaussianProduct (naturalPast κ) (physicalPast κ) (natural_le_physical κ) _
    (changed_brownian_martingale κ) (state_stronglyAdapted κ)

theorem augmented_natural_martingale (κ : ℝ≥0) :
    Martingale (fun t ω => changedPath κ ω t) (augmentedNaturalPast κ) gaussianProduct :=
  AmbientMartingaleModification.martingale_augmented gaussianProduct (naturalPast κ) _
    (natural_martingale κ)

theorem square_natural_martingale (κ : ℝ≥0) :
    Martingale (fun t ω => (changedPath κ ω t)^2-(inverse κ ω t : ℝ))
      (augmentedNaturalPast κ) gaussianProduct := by
  have hm := AmbientMartingaleModification.martingale_augmented gaussianProduct
    (physicalPast κ) _ (changed_square_martingale κ)
  apply shrink gaussianProduct (augmentedNaturalPast κ) _ (augmented_le_physical κ) _ hm
  intro t
  exact (((state_augmented_adapted κ t).measurable.pow_const 2).sub
    (continuous_subtype_val.measurable.comp (inverse_observed_past κ t))).stronglyMeasurable

end OperatorDerivativeRewrite.Foundation.StickyNaturalMartingales
