import Foundation.HigherHeatUnboundedExpectation

/-! Higher even heat cylinder expectations have no bounded-function or finite-variation complex extension. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatComplexObstruction
open HigherHeatContinuousCylinders HigherHeatPathCylinderAlgebra HigherHeatUnboundedExpectation

theorem no_continuous_extension (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T)
    (L : (Path →ᵇ ℝ) →L[ℝ] ℝ) :
    ¬ ∀ F : cylinderAlgebra, L F.val=algebraExpectation m (by omega) T hT F := by
  intro h
  apply no_uniform_bound m hm T hT
  refine ⟨‖L‖,fun F => ?_⟩
  have hb := L.le_opNorm F.val
  rw [h F,Real.norm_eq_abs] at hb
  exact hb

theorem no_complex_measure (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T)
    (μ : VectorMeasure Path ℂ) [IsFiniteMeasure μ.variation] :
    ¬ ∀ F : cylinderAlgebra, (algebraExpectation m (by omega) T hT F : ℂ)=
      ∫ᵛ ω : Path, F.val ω ∂•μ := by
  intro h
  apply no_uniform_bound m hm T hT
  refine ⟨‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)‖*μ.variation.real Set.univ,fun F => ?_⟩
  have hb := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := μ) (B := ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ))
    (f := fun ω : Path => F.val ω)
    (Eventually.of_forall fun ω => F.val.norm_coe_le_norm ω)
  rw [← h F] at hb
  simpa only [Complex.norm_real,Real.norm_eq_abs,mul_assoc,mul_left_comm,mul_comm] using hb

end OperatorDerivativeRewrite.Foundation.HigherHeatComplexObstruction
