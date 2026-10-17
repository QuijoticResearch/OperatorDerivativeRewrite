import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! Measurable continuous random-time composition without a probability or Gaussian assumption. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ContinuousRandomTimeComposition
variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  (X : Ω → C(ℝ, ℝ)) (Y : Ξ → C(ℝ≥0, ℝ))

def path (ω : Ω × Ξ) : C(ℝ≥0, ℝ) := (X ω.1).comp (Y ω.2)

def value (t : ℝ≥0) (ω : Ω × Ξ) : ℝ := path X Y ω t

omit [MeasurableSpace Ω] [MeasurableSpace Ξ] in
theorem value_eq (t : ℝ≥0) (ω : Ω × Ξ) : value X Y t ω = X ω.1 (Y ω.2 t) := rfl

omit [MeasurableSpace Ω] [MeasurableSpace Ξ] in
theorem value_continuous (ω : Ω × Ξ) : Continuous (fun t => value X Y t ω) :=
  (path X Y ω).continuous

theorem value_measurable (hX : Measurable X) (hY : Measurable Y) (t : ℝ≥0) :
    Measurable (value X Y t) := by
  have hx : Measurable (fun ω : Ω × Ξ => X ω.1) := hX.comp measurable_fst
  have hy : Measurable (fun ω : Ω × Ξ => Y ω.2 t) :=
    (ContinuousMap.measurable_eval t).comp (hY.comp measurable_snd)
  exact continuous_eval.measurable.comp (hx.prodMk hy)

theorem path_measurable (hX : Measurable X) (hY : Measurable Y) : Measurable (path X Y) :=
  ContinuousMap.measurable_iff_eval.mpr (value_measurable X Y hX hY)

theorem jointly_measurable (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun p : ℝ≥0 × (Ω × Ξ) => value X Y p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable (value_continuous X Y)
    (value_measurable X Y hX hY)

end OperatorDerivativeRewrite.Foundation.ContinuousRandomTimeComposition
