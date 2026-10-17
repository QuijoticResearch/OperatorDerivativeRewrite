import Foundation.ExponentialJointDisintegration

/-! Positive normalized exponential interaction preserves boundary null sets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace OperatorDerivativeRewrite.Foundation.ExponentialBoundaryEquivalence
open ExponentialJointDisintegration MeasurableExponentialKernel
variable {P E : Type*} [MeasurableSpace P] [MeasurableSpace E]
variable (ρ : Measure P) (μ : Measure E) [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
variable (X : P → E → ℝ)

theorem reverse_ac (hX : Measurable (Function.uncurry X))
    (hI : ∀ p, Integrable (fun x => Real.exp (X p x)) μ)
    (hJ : Integrable (fun z : P × E => Real.exp (X z.1 z.2)) (ρ.prod μ)) :
    ρ ≪ boundary ρ μ X := by
  apply withDensity_absolutelyContinuous'
    (boundaryDensity_measurable ρ μ X hX).ennreal_ofReal.aemeasurable
  filter_upwards with p
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  exact div_pos (partition_positive μ X p (hI p)) (total_positive ρ μ X hJ)

theorem null_iff (hX : Measurable (Function.uncurry X))
    (hI : ∀ p, Integrable (fun x => Real.exp (X p x)) μ)
    (hJ : Integrable (fun z : P × E => Real.exp (X z.1 z.2)) (ρ.prod μ)) (s : Set P) :
    boundary ρ μ X s = 0 ↔ ρ s = 0 :=
  ⟨fun h => reverse_ac ρ μ X hX hI hJ h,
    fun h => withDensity_absolutelyContinuous ρ _ h⟩

end OperatorDerivativeRewrite.Foundation.ExponentialBoundaryEquivalence
