import Foundation.L2GeneratedSubspace
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Coordinatewise AE modifications preserve real-valued measurable
functionals and generated L2 spaces, even for an uncountable observation family.
The argument is per measurable event, not a false simultaneous all-index event. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GeneratedFamilyModification
variable {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (X Y : Ω → I → ℝ) (hXY : ∀ i, (fun ω => X ω i) =ᵐ[μ] fun ω => Y ω i)
include hXY

theorem preimage_ae (S : Set (I → ℝ)) (hS : MeasurableSet S) :
    ∀ᵐ ω ∂μ, X ω ∈ S ↔ Y ω ∈ S := by
  refine MeasurableSpace.induction_on_inter
    (C := fun S _ => ∀ᵐ ω ∂μ, X ω ∈ S ↔ Y ω ∈ S)
    (generateFrom_measurableCylinders (α := fun _ : I => ℝ)).symm
    isPiSystem_measurableCylinders (by simp) ?_ ?_ ?_ S hS
  · intro A hA
    obtain ⟨s, A, hA, rfl⟩ := (mem_measurableCylinders A).mp hA
    filter_upwards [ae_all_iff.mpr (fun i : s => hXY i.val)] with ω he
    change (fun i : s => X ω i.val) ∈ A ↔ (fun i : s => Y ω i.val) ∈ A
    rw [show (fun i : s => X ω i.val) = (fun i : s => Y ω i.val) from funext he]
  · intro A hA he
    filter_upwards [he] with ω hω
    exact not_congr hω
  · intro A hd hm he
    filter_upwards [ae_all_iff.mpr he] with ω hω
    simp only [mem_iUnion]
    exact exists_congr (fun n => hω n)

theorem functional_ae (g : (I → ℝ) → ℝ) (hg : Measurable g) :
    (fun ω => g (X ω)) =ᵐ[μ] fun ω => g (Y ω) := by
  have hq (q : ℚ) : ∀ᵐ ω ∂μ, (q : ℝ) < g (X ω) ↔ (q : ℝ) < g (Y ω) :=
    preimage_ae μ X Y hXY (g ⁻¹' Ioi (q : ℝ)) (hg measurableSet_Ioi)
  filter_upwards [ae_all_iff.mpr hq] with ω hω
  exact eq_of_forall_rat_lt_iff_lt hω

theorem aestronglyMeasurable_transfer {F : Ω → ℝ}
    (hF : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] F μ) :
    AEStronglyMeasurable[MeasurableSpace.comap Y inferInstance] F μ := by
  obtain ⟨g, hg, he⟩ := hF.stronglyMeasurable_mk.exists_eq_measurable_comp
  have hm : StronglyMeasurable[MeasurableSpace.comap Y inferInstance] (g ∘ Y) :=
    hg.comp_measurable (Measurable.of_comap_le le_rfl)
  have hfg : F =ᵐ[μ] g ∘ X := he ▸ hF.ae_eq_mk
  have hmod := functional_ae μ X Y hXY g hg.measurable
  exact hm.aestronglyMeasurable.congr (hfg.trans hmod).symm

theorem lpMeas_eq : lpMeas ℝ ℝ (MeasurableSpace.comap X inferInstance) 2 μ =
    lpMeas ℝ ℝ (MeasurableSpace.comap Y inferInstance) 2 μ := by
  apply le_antisymm
  · intro F hF
    exact aestronglyMeasurable_transfer μ X Y hXY hF
  · intro F hF
    exact aestronglyMeasurable_transfer μ Y X (fun i => (hXY i).symm) hF

end OperatorDerivativeRewrite.Foundation.GeneratedFamilyModification
