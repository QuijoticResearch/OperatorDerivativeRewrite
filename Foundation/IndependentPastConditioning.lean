import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalProbability

/-! Conditioning on an event in the past preserves an independent future
sigma-algebra and its independence from that past, with actual probability laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace OperatorDerivativeRewrite.Foundation.IndependentPastConditioning
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω)
  [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem event_probability (h₁ : m₁ ≤ m₀) (hI : Indep m₁ m₂ μ)
    (A : Set Ω) (hA : MeasurableSet[m₂] A) (hμA : μ A ≠ 0)
    (S : Set Ω) (hS : MeasurableSet[m₁] S) : μ[|A] S = μ S := by
  rw [cond_apply' (h₁ S hS),
    (hI.symm.indepSet_of_measurableSet hA hS).measure_inter_eq_mul,
    ← mul_assoc,ENNReal.inv_mul_cancel hμA (measure_ne_top μ A),one_mul]

theorem independence (h₁ : m₁ ≤ m₀) (h₂ : m₂ ≤ m₀) (hI : Indep m₁ m₂ μ)
    (A : Set Ω) (hA : MeasurableSet[m₂] A) (hμA : μ A ≠ 0) :
    Indep m₁ m₂ μ[|A] := by
  letI : IsProbabilityMeasure μ[|A] := cond_isProbabilityMeasure hμA
  apply (indep_iff_forall_indepSet μ[|A]).mpr
  intro S T hS hT
  apply (indepSet_iff_measure_inter_eq_mul (h₁ S hS) (h₂ T hT) μ[|A]).mpr
  rw [event_probability m₁ m₂ μ h₁ hI A hA hμA S hS,
    cond_apply' ((h₁ S hS).inter (h₂ T hT)),cond_apply' (h₂ T hT)]
  rw [Set.inter_left_comm,
    (hI.indepSet_of_measurableSet hS (hA.inter hT)).measure_inter_eq_mul]
  ring

theorem map_law {E : Type*} [MeasurableSpace E] (X : Ω → E)
    (hX : Measurable[m₁] X) (h₁ : m₁ ≤ m₀) (hI : Indep m₁ m₂ μ)
    (A : Set Ω) (hA : MeasurableSet[m₂] A) (hμA : μ A ≠ 0) :
    μ[|A].map X = μ.map X := by
  ext B hB
  rw [Measure.map_apply (hX.mono h₁ le_rfl) hB,Measure.map_apply (hX.mono h₁ le_rfl) hB]
  exact event_probability m₁ m₂ μ h₁ hI A hA hμA _ (hX hB)

end OperatorDerivativeRewrite.Foundation.IndependentPastConditioning
