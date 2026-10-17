import Foundation.GaussianCore
import Foundation.DiagonalAmbientNullity
import Foundation.HilbertRepresentation

/-! Actual probability references with diagonal mass and compatible one-coordinate marginals. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.DiagonalReferenceProbability
set_option backward.isDefEq.respectTransparency false
variable {α : Type*} [MeasurableSpace α]

def diagonalMap (x : α) : α × α := (x,x)

theorem diagonal_measurable : Measurable (diagonalMap : α → α × α) :=
  measurable_id.prodMk measurable_id

def diagonalLaw (μ : Measure α) : Measure (α × α) := Measure.map diagonalMap μ

theorem diagonal_first (μ : Measure α) : Measure.map Prod.fst (diagonalLaw μ) = μ := by
  rw [diagonalLaw, Measure.map_map measurable_fst diagonal_measurable]
  exact Measure.map_id

theorem diagonal_second (μ : Measure α) : Measure.map Prod.snd (diagonalLaw μ) = μ := by
  rw [diagonalLaw, Measure.map_map measurable_snd diagonal_measurable]
  exact Measure.map_id

theorem coefficient_sum (p : ℝ≥0) (hp : p ≤ 1) :
    ((1-p : ℝ≥0) : ℝ≥0∞) + (p : ℝ≥0∞) = 1 := by
  rw [← ENNReal.coe_add, tsub_add_cancel_of_le hp]
  rfl

def reference (μ : Measure α) (p : ℝ≥0) : Measure (α × α) :=
  ((1-p : ℝ≥0) : ℝ≥0∞) • μ.prod μ + (p : ℝ≥0∞) • diagonalLaw μ

theorem first_marginal (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ℝ≥0) (hp : p ≤ 1) : Measure.map Prod.fst (reference μ p) = μ := by
  rw [reference, Measure.map_add _ _ measurable_fst,
    Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_fst_prod, measure_univ,
    one_smul, diagonal_first, ← add_smul, coefficient_sum p hp, one_smul]

theorem second_marginal (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ℝ≥0) (hp : p ≤ 1) : Measure.map Prod.snd (reference μ p) = μ := by
  rw [reference, Measure.map_add _ _ measurable_snd,
    Measure.map_smul _ measurable_snd.aemeasurable,
    Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_snd_prod, measure_univ,
    one_smul, diagonal_second, ← add_smul, coefficient_sum p hp, one_smul]

theorem first_preserving (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ℝ≥0) (hp : p ≤ 1) : MeasurePreserving Prod.fst (reference μ p) μ :=
  ⟨measurable_fst, first_marginal μ p hp⟩

theorem second_preserving (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ℝ≥0) (hp : p ≤ 1) : MeasurePreserving Prod.snd (reference μ p) μ :=
  ⟨measurable_snd, second_marginal μ p hp⟩

def firstEmbedding (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ℝ≥0) (hp : p ≤ 1) : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (reference μ p) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst (first_preserving μ p hp)

theorem firstEmbedding_coeFn (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ℝ≥0) (hp : p ≤ 1) (f : Lp ℝ 2 μ) :
    firstEmbedding μ p hp f =ᵐ[reference μ p] fun z => f z.1 :=
  Lp.coeFn_compMeasurePreserving f (first_preserving μ p hp)

def firstAdjoint (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ℝ≥0) (hp : p ≤ 1) : Lp ℝ 2 (reference μ p) →L[ℝ] Lp ℝ 2 μ :=
  HilbertRepresentation.predictableAdjoint (firstEmbedding μ p hp)

theorem firstAdjoint_embedding (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ℝ≥0) (hp : p ≤ 1) (f : Lp ℝ 2 μ) :
    firstAdjoint μ p hp (firstEmbedding μ p hp f) = f :=
  HilbertRepresentation.predictableAdjoint_isometry_apply (firstEmbedding μ p hp) f

theorem probability (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ℝ≥0) (hp : p ≤ 1) : IsProbabilityMeasure (reference μ p) where
  measure_univ := by
    rw [reference, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      diagonalLaw, Measure.map_apply diagonal_measurable MeasurableSet.univ]
    simpa only [Set.preimage_univ, measure_univ, smul_eq_mul, mul_one] using coefficient_sum p hp

theorem diagonal_swap (μ : Measure α) :
    Measure.map Prod.swap (diagonalLaw μ) = diagonalLaw μ := by
  rw [diagonalLaw, Measure.map_map measurable_swap diagonal_measurable]
  rfl

theorem exchangeable (μ : Measure α) [IsProbabilityMeasure μ] (p : ℝ≥0) :
    Measure.map Prod.swap (reference μ p) = reference μ p := by
  rw [reference, Measure.map_add _ _ measurable_swap,
    Measure.map_smul _ measurable_swap.aemeasurable,
    Measure.map_smul _ measurable_swap.aemeasurable, Measure.prod_swap, diagonal_swap]

theorem real_diagonal_mass (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (p : ℝ≥0) : reference μ p DiagonalAmbientNullity.diagonal = (p : ℝ≥0∞) := by
  have hprod : μ.prod μ DiagonalAmbientNullity.diagonal = 0 := by
    rw [Measure.prod_apply DiagonalAmbientNullity.diagonal_measurable]
    simp only [DiagonalAmbientNullity.diagonal_slice, measure_singleton, lintegral_zero]
  have hd : diagonalLaw μ DiagonalAmbientNullity.diagonal = 1 := by
    rw [diagonalLaw, Measure.map_apply diagonal_measurable
      DiagonalAmbientNullity.diagonal_measurable]
    have hpre : (diagonalMap : ℝ → ℝ × ℝ) ⁻¹' DiagonalAmbientNullity.diagonal = Set.univ := by
      ext x
      simp [diagonalMap, DiagonalAmbientNullity.diagonal]
    rw [hpre, measure_univ]
  rw [reference, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hprod, hd]
  simp

theorem gaussian_diagonal_mass (p : ℝ≥0) :
    reference GaussianCore.γ p DiagonalAmbientNullity.diagonal = (p : ℝ≥0∞) := by
  have : NullSingletonClass GaussianCore.γ := ⟨fun x =>
    (ProbabilityTheory.gaussianReal_absolutelyContinuous 0 (by norm_num)) (by simp)⟩
  exact real_diagonal_mass GaussianCore.γ p

end OperatorDerivativeRewrite.Foundation.DiagonalReferenceProbability
