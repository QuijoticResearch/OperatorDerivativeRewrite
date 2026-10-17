import Foundation.HigherHeatPositionVariation
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Matching actual cylinder expectations forces marginals, excluding finite signed path realizations. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSignedRepresentation
open HigherHeatDyadicLaws HigherHeatCylindricalExpectation HigherHeatContinuousCylinders
open HigherHeatPathCylinderAlgebra HigherHeatPositionVariation

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem bounded_real_integrable (ν : SignedMeasure X) (f : X →ᵇ ℝ) : ν.Integrable f := by
  letI : IsFiniteMeasure ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  exact Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Eventually.of_forall f.norm_coe_le_norm)

theorem positive_integrable (μ : Measure X) [IsFiniteMeasure μ] (f : X →ᵇ ℝ) : Integrable f μ :=
  Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Eventually.of_forall f.norm_coe_le_norm)

theorem real_integral_toSigned (μ : Measure X) [IsFiniteMeasure μ] (f : X →ᵇ ℝ) :
    (∫ᵛ x, f x ∂•μ.toSignedMeasure)=∫ x, f x ∂μ := by
  have he : (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
    ext x y
    simp [smul_eq_mul,mul_comm]
  change VectorMeasure.integral μ.toSignedMeasure f (ContinuousLinearMap.lsmul ℝ ℝ) = _
  rw [← he,VectorMeasure.integral_toSignedMeasure]

theorem integral_jordan (ν : SignedMeasure X) (f : X →ᵇ ℝ) :
    (∫ᵛ x, f x ∂•ν)=(∫ x, f x ∂ν.toJordanDecomposition.posPart)-
      ∫ x, f x ∂ν.toJordanDecomposition.negPart := by
  conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure,VectorMeasure.integral_sub_vectorMeasure
    (bounded_real_integrable _ f) (bounded_real_integrable _ f),
    real_integral_toSigned,real_integral_toSigned]

theorem signed_ext_bounded [HasOuterApproxClosed X] (ν μ : SignedMeasure X)
    (h : ∀ f : X →ᵇ ℝ, (∫ᵛ x, f x ∂•ν)=(∫ᵛ x, f x ∂•μ)) : ν=μ := by
  have he : ν.toJordanDecomposition.posPart+μ.toJordanDecomposition.negPart =
      μ.toJordanDecomposition.posPart+ν.toJordanDecomposition.negPart := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_add_measure (positive_integrable _ f) (positive_integrable _ f),
      integral_add_measure (positive_integrable _ f) (positive_integrable _ f)]
    have hf := h f
    rw [integral_jordan,integral_jordan] at hf
    exact sub_eq_sub_iff_add_eq_add.mp hf
  ext A hA
  rw [SignedMeasure.apply_eq_posPart_real_sub_negPart_real _ hA,
    SignedMeasure.apply_eq_posPart_real_sub_negPart_real _ hA]
  have hv := congrArg (fun ρ : Measure X => ρ.real A) he
  rw [measureReal_add_apply,measureReal_add_apply] at hv
  exact sub_eq_sub_iff_add_eq_add.mpr hv

theorem marginal_of_representation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (μ : SignedMeasure Path)
    (h : ∀ F : cylinderAlgebra, algebraExpectation m hm T hT F=∫ᵛ ω : Path, F.val ω ∂•μ)
    (n : ℕ) : μ.map (sample n)=HigherHeatDyadicLaws.law m hm T hT n := by
  apply signed_ext_bounded
  intro f
  have hi := bounded_real_integrable μ (sampleLift n f)
  have hf := h (representCylinder (cylinderOf n f))
  rw [algebraExpectation_represent,cylindricalExpectation_apply] at hf
  change (∫ᵛ x : Grid n, f x ∂•HigherHeatDyadicLaws.law m hm T hT n) =
    ∫ᵛ ω : Path, f (sample n ω) ∂•μ at hf
  rw [VectorMeasure.integral_map (sample_continuous n).measurable f.continuous.aestronglyMeasurable hi]
  exact hf.symm

theorem no_signed_observable_realization (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T)
    (μ : SignedMeasure Path) :
    ¬ ∀ F : cylinderAlgebra, algebraExpectation m (by omega) T hT F=∫ᵛ ω : Path, F.val ω ∂•μ := by
  intro h
  exact no_signed_continuous_path_marginals m hm T hT μ
    (fun n => marginal_of_representation m (by omega) T hT μ h n)

end OperatorDerivativeRewrite.Foundation.HigherHeatSignedRepresentation
