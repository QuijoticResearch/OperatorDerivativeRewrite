import Foundation.AmbientNullAugmentation
import Mathlib.Probability.Independence.Basic

/-! Independence survives the specified ambient null augmentation. Events
are transferred through actual almost-everywhere versions, not completed by fiat. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace OperatorDerivativeRewrite.Foundation.AmbientIndependenceAugmentation
open AmbientNullAugmentation
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω)
  [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem augment_right (h₁ : m₁ ≤ m₀) (hI : Indep m₁ m₂ μ) :
    Indep m₁ (augment m₂ μ) μ := by
  apply (indep_iff_forall_indepSet μ).mpr
  intro S A hS hA
  obtain ⟨hAamb,A₀,hA₀,he⟩ := hA
  apply (indepSet_iff_measure_inter_eq_mul (h₁ S hS) hAamb μ).mpr
  have hinter : S ∩ A =ᵐ[μ] S ∩ A₀ :=
    (he.mono (fun ω h => show ω ∈ S ∩ A ↔ ω ∈ S ∩ A₀ from and_congr Iff.rfl h)).set_eq
  calc
    μ (S ∩ A) = μ (S ∩ A₀) := measure_congr hinter
    _ = μ S*μ A₀ := (hI.indepSet_of_measurableSet hS hA₀).measure_inter_eq_mul
    _ = μ S*μ A := congrArg (fun z => μ S*z) (measure_congr he.set_eq).symm

theorem augment_left (h₂ : m₂ ≤ m₀) (hI : Indep m₁ m₂ μ) :
    Indep (augment m₁ μ) m₂ μ :=
  (augment_right m₂ m₁ μ h₂ hI.symm).symm

theorem augment_both (_h₁ : m₁ ≤ m₀) (h₂ : m₂ ≤ m₀) (hI : Indep m₁ m₂ μ) :
    Indep (augment m₁ μ) (augment m₂ μ) μ :=
  augment_right (augment m₁ μ) m₂ μ (le_ambient m₁ μ)
    (augment_left m₁ m₂ μ h₂ hI)

omit [IsProbabilityMeasure μ] in
theorem smaller_right (m₂' : MeasurableSpace Ω) (hle : m₂' ≤ m₂) (hI : Indep m₁ m₂ μ) :
    Indep m₁ m₂' μ := by
  apply (indep_iff_forall_indepSet μ).mpr
  intro S A hS hA
  exact hI.indepSet_of_measurableSet hS (hle A hA)

end OperatorDerivativeRewrite.Foundation.AmbientIndependenceAugmentation
