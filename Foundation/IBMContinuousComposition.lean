import Foundation.IBMSourceLaws
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! Composition of independently specified measurable continuous source paths.
The path maps must still be constructed as modifications of IBMSourceLaws;
this module proves their random-time composition is an actual process. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMContinuousComposition
open IBMSourceLaws InfiniteGaussian

variable (X : SampleSpace → C(ℝ, ℝ)) (Y : SampleSpace → C(ℝ≥0, ℝ))

/-- A continuous path for every joint sample, built from the supplied paths. -/
def path (ω : JointSample) : C(ℝ≥0, ℝ) :=
  ⟨fun t => X ω.1 |Y ω.2 t|,
    (X ω.1).continuous.comp ((continuous_abs).comp (Y ω.2).continuous)⟩

def value (t : ℝ≥0) (ω : JointSample) : ℝ := path X Y ω t

theorem path_continuous (ω : JointSample) : Continuous (fun t => value X Y t ω) :=
  (path X Y ω).continuous

theorem value_eq (t : ℝ≥0) (ω : JointSample) :
    value X Y t ω = X ω.1 |Y ω.2 t| := rfl

theorem sources_independent (hX : Measurable X) (hY : Measurable Y) :
    IndepFun (fun ω : JointSample => X ω.1)
      (fun ω : JointSample => Y ω.2) jointMeasure :=
  indepFun_prod hX hY

theorem value_measurable (hX : Measurable X) (hY : Measurable Y) (t : ℝ≥0) :
    Measurable (value X Y t) := by
  change Measurable (fun ω : JointSample => X ω.1 |Y ω.2 t|)
  have hmX : Measurable (fun ω : JointSample => X ω.1) := hX.comp measurable_fst
  have hmY : Measurable (fun ω : JointSample => |Y ω.2 t|) :=
    continuous_abs.measurable.comp ((ContinuousMap.measurable_eval t).comp (hY.comp measurable_snd))
  exact (continuous_eval.measurable).comp (hmX.prodMk hmY)

theorem path_measurable (hX : Measurable X) (hY : Measurable Y) :
    Measurable (path X Y) :=
  ContinuousMap.measurable_iff_eval.mpr (value_measurable X Y hX hY)

/-- Joint time/sample measurability on the actual joint source space. -/
theorem value_jointly_measurable (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun p : ℝ≥0 × JointSample => value X Y p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable (path_continuous X Y)
    (value_measurable X Y hX hY)

theorem value_zero (hX0 : ∀ ω, X ω 0 = 0) (hY0 : ∀ ω, Y ω 0 = 0)
    (ω : JointSample) : value X Y 0 ω = 0 := by
  simp [value_eq, hY0, hX0]

end OperatorDerivativeRewrite.Foundation.IBMContinuousComposition
