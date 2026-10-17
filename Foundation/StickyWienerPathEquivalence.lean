import Foundation.AmbientNullVersions
import Foundation.StickyBrownianRecovery
import Foundation.StickyWienerPathRealization

/-! The actual sticky and Wiener path laws are related by Borel maps that
are inverses modulo their respective null sets. This is a whole-path result,
not an identification of the physical-time filtrations or generators. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyWienerPathEquivalence
open InfiniteGaussian IBMConstructedSources BrownianMassRandomTimeChange
open StickyBrownianRecovery StickyWienerPathRealization
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

theorem exists_recovery (κ : ℝ≥0) : ∃ R : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ),
    Measurable R ∧ (fun ω => R (changedPath κ ω)) =ᵐ[gaussianProduct] clockPath := by
  have hf : StronglyMeasurable[observedAug κ] clockPath :=
    (brownian_path_observed κ).stronglyMeasurable
  obtain ⟨R,hR,he⟩ := AmbientNullVersions.exists_raw_factor gaussianProduct
    (changedPath κ) clockPath hf
  exact ⟨R,hR.measurable,he.symm⟩

def recovery (κ : ℝ≥0) : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) :=
  Classical.choose (exists_recovery κ)

theorem recovery_measurable (κ : ℝ≥0) : Measurable (recovery κ) :=
  (Classical.choose_spec (exists_recovery κ)).1

theorem recovery_agrees (κ : ℝ≥0) :
    (fun ω => recovery κ (changedPath κ ω)) =ᵐ[gaussianProduct] clockPath :=
  (Classical.choose_spec (exists_recovery κ)).2

def wienerLaw : Measure C(ℝ≥0, ℝ) := gaussianProduct.map clockPath

def stickyLaw (κ : ℝ≥0) : Measure C(ℝ≥0, ℝ) := gaussianProduct.map (changedPath κ)

theorem sticky_preserving (κ : ℝ≥0) :
    MeasurePreserving (stickyPath κ) wienerLaw (stickyLaw κ) :=
  ⟨stickyPath_measurable κ,stickyPath_law κ⟩

theorem recovery_preserving (κ : ℝ≥0) :
    MeasurePreserving (recovery κ) (stickyLaw κ) wienerLaw := by
  refine ⟨recovery_measurable κ,?_⟩
  rw [stickyLaw,Measure.map_map (recovery_measurable κ) (changedPath_measurable κ)]
  exact Measure.map_congr (recovery_agrees κ)

theorem left_inverse_ae (κ : ℝ≥0) : ∀ᵐ p ∂wienerLaw,
    recovery κ (stickyPath κ p) = p := by
  apply (ae_map_iff clockPath_measurable.aemeasurable
    (measurableSet_eq_fun ((recovery_measurable κ).comp (stickyPath_measurable κ))
      measurable_id)).mpr
  filter_upwards [stickyPath_agrees,recovery_agrees κ] with ω hs hr
  simpa only [Function.comp_apply,id_eq,hs κ] using hr

theorem right_inverse_ae (κ : ℝ≥0) : ∀ᵐ p ∂stickyLaw κ,
    stickyPath κ (recovery κ p) = p := by
  apply (ae_map_iff (changedPath_measurable κ).aemeasurable
    (measurableSet_eq_fun ((stickyPath_measurable κ).comp (recovery_measurable κ))
      measurable_id)).mpr
  filter_upwards [stickyPath_agrees,recovery_agrees κ] with ω hs hr
  simpa only [Function.comp_apply,id_eq,hr] using hs κ

end OperatorDerivativeRewrite.Foundation.StickyWienerPathEquivalence
