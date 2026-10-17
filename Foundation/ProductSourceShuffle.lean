import Mathlib.MeasureTheory.Measure.Prod

/-! Regroup independent holding/mark pasts and futures without changing their actual law. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.ProductSourceShuffle
variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

def shuffle (p : (A × B) × (C × D)) : (A × C) × (B × D) :=
  ((p.1.1,p.2.1),(p.1.2,p.2.2))

theorem preserving (μA : Measure A) (μB : Measure B) (μC : Measure C) (μD : Measure D)
    [IsProbabilityMeasure μA] [IsProbabilityMeasure μB]
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μD] :
    MeasurePreserving shuffle ((μA.prod μB).prod (μC.prod μD))
      ((μA.prod μC).prod (μB.prod μD)) := by
  have h₁ := measurePreserving_prodAssoc μA μB (μC.prod μD)
  have h₂ := (measurePreserving_prodAssoc μB μC μD).symm
  have h₃ := (Measure.measurePreserving_swap (μ := μB) (ν := μC)).prod (MeasurePreserving.id μD)
  have h₄ := measurePreserving_prodAssoc μC μB μD
  have hm := (MeasurePreserving.id μA).prod (h₄.comp (h₃.comp h₂))
  have h₅ := (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm
  exact h₅.comp (hm.comp h₁)

end OperatorDerivativeRewrite.Foundation.ProductSourceShuffle
