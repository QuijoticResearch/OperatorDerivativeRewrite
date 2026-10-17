import Foundation.DiagonalAmbientNullity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! A nonzero diagonal probability measure is singular to the ambient product law. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.DiagonalMeasureSeparation
open DiagonalAmbientNullity
set_option backward.isDefEq.respectTransparency false

def diagonalMap (x : ℝ) : ℝ × ℝ := (x,x)

theorem diagonalMap_measurable : Measurable diagonalMap :=
  measurable_id.prodMk measurable_id

def diagonalLaw : Measure (ℝ × ℝ) :=
  Measure.map diagonalMap (volume.restrict (Set.Icc (0 : ℝ) 1))

instance diagonalLaw_probability : IsProbabilityMeasure diagonalLaw where
  measure_univ := by
    rw [diagonalLaw, Measure.map_apply diagonalMap_measurable MeasurableSet.univ]
    simp

theorem diagonalLaw_diagonal : diagonalLaw diagonal = 1 := by
  rw [diagonalLaw, Measure.map_apply diagonalMap_measurable diagonal_measurable]
  have he : diagonalMap ⁻¹' diagonal = Set.univ := by
    ext x
    simp [diagonalMap, diagonal]
  rw [he]
  simp

theorem diagonalLaw_not_absolutelyContinuous : ¬ diagonalLaw ≪ plane := by
  intro h
  have hz := h plane_diagonal_zero
  rw [diagonalLaw_diagonal] at hz
  norm_num at hz

theorem diagonalLaw_no_ambient_density (ρ : ℝ × ℝ → ℝ≥0∞) :
    diagonalLaw ≠ plane.withDensity ρ := by
  intro h
  apply diagonalLaw_not_absolutelyContinuous
  rw [h]
  exact withDensity_absolutelyContinuous _ _

theorem diagonalValue_integral_ambient (c : ℝ) :
    (∫ x, diagonalValue c x ∂plane) = 0 := by
  rw [integral_congr_ae (diagonalValue_ae_zero c)]
  exact integral_zero _ _

theorem diagonalValue_integral_diagonal (c : ℝ) :
    (∫ x, diagonalValue c x ∂diagonalLaw) = c := by
  have hm : Measurable (diagonalValue c) := measurable_const.indicator diagonal_measurable
  rw [diagonalLaw, integral_map diagonalMap_measurable.aemeasurable hm.aestronglyMeasurable]
  change (∫ x : ℝ, diagonalValue c (x,x) ∂volume.restrict (Set.Icc (0 : ℝ) 1)) = c
  simp only [diagonalValue_on]
  rw [integral_const]
  simp [measureReal_def]

/-- Even an arbitrary nonlinear function of the ambient L2 class cannot recover this pairing. -/
theorem no_ambient_L2_diagonal_recovery :
    ¬ ∃ T : Lp ℝ 2 plane → ℝ, ∀ c : ℝ,
      T ((diagonalValue_memLp c 2).toLp (diagonalValue c)) =
        ∫ x, diagonalValue c x ∂diagonalLaw := by
  rintro ⟨T,hT⟩
  have h0 := hT 0
  have h1 := hT 1
  rw [diagonalValue_toL2_zero, diagonalValue_integral_diagonal] at h0 h1
  linarith

end OperatorDerivativeRewrite.Foundation.DiagonalMeasureSeparation
