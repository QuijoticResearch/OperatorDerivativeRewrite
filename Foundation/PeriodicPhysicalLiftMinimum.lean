import Foundation.PeriodicCorrectedPhysicalLift

/-! Unique minimum-norm physical lift, and the strict cost of the physical correction. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicPhysicalLiftMinimum
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarsePhysicalSector PeriodicCoarsePhysicalBounds
open PeriodicFinePhysicalProjection PeriodicProjectedCoarseLift PeriodicProjectedCoarseGram
open PeriodicCorrectedPhysicalLift
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def fineSize (f : Edge → ℝ) : ℝ := dotProduct f f

theorem fineSize_nonneg (f : Edge → ℝ) : 0 ≤ fineSize f := by
  change 0 ≤ ∑ e, f e * f e
  exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

theorem corrected_orthogonal_residual (c : physicalSpace) (f : Edge → ℝ)
    (hf : ∀ g : Edge → ℝ, incidence g = 0 → dotProduct f g = 0)
    (ha : average f = c.val) : dotProduct (f - correctedLift c) (correctedLift c) = 0 := by
  have hr : ∀ g : Edge → ℝ, incidence g = 0 →
      dotProduct (f - correctedLift c) g = 0 := by
    intro g hg
    rw [sub_dotProduct, hf g hg, correctedLift_physical c g hg, sub_self]
  have hav : average (f - correctedLift c) = 0 := by
    rw [map_sub, ha, correctedLift_average, sub_self]
  have he := projected_adjoint (multiplier c).val (f - correctedLift c) hr
  rw [hav, zero_dotProduct] at he
  exact he

theorem physical_completed_square (c : physicalSpace) (f : Edge → ℝ)
    (hf : ∀ g : Edge → ℝ, incidence g = 0 → dotProduct f g = 0)
    (ha : average f = c.val) :
    fineSize f = fineSize (correctedLift c) + fineSize (f - correctedLift c) := by
  have ho := corrected_orthogonal_residual c f hf ha
  rw [sub_dotProduct] at ho
  unfold fineSize
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub,
    dotProduct_comm (correctedLift c) f]
  linarith

theorem physical_minimum (c : physicalSpace) (f : Edge → ℝ)
    (hf : ∀ g : Edge → ℝ, incidence g = 0 → dotProduct f g = 0)
    (ha : average f = c.val) : fineSize (correctedLift c) ≤ fineSize f := by
  rw [physical_completed_square c f hf ha]
  exact le_add_of_nonneg_right (fineSize_nonneg _)

theorem physical_minimum_unique (c : physicalSpace) (f : Edge → ℝ)
    (hf : ∀ g : Edge → ℝ, incidence g = 0 → dotProduct f g = 0)
    (ha : average f = c.val) :
    fineSize f = fineSize (correctedLift c) ↔ f = correctedLift c := by
  constructor
  · intro he
    have hs := physical_completed_square c f hf ha
    have hz : fineSize (f - correctedLift c) = 0 := by linarith
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hz)
  · intro h
    rw [h]

theorem corrected_size (c : physicalSpace) :
    fineSize (correctedLift c) = dotProduct c.val (multiplier c).val := by
  have h := projected_adjoint (multiplier c).val (correctedLift c) (correctedLift_physical c)
  rw [correctedLift_average] at h
  exact h

theorem unrestricted_completed_square (c : PeriodicCoarseWalshBasis.Field) (f : Edge → ℝ)
    (ha : average f = c) :
    fineSize f = 8 * size c + fineSize (f - (8 : ℝ) • normalizedLift c) := by
  have hl := hilbertLift_norm_sq c
  rw [← real_inner_self_eq_norm_sq, inner_raw, raw_hilbertLift] at hl
  have hfc : dotProduct f (normalizedLift c) = size c := by
    rw [lift_is_adjoint, ha]
    rfl
  unfold fineSize
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (normalizedLift c) f, hfc, hl]
  ring

theorem unrestricted_minimum_equality (c : PeriodicCoarseWalshBasis.Field) (f : Edge → ℝ)
    (ha : average f = c) :
    fineSize f = 8 * size c ↔ f = (8 : ℝ) • normalizedLift c := by
  constructor
  · intro he
    have hs := unrestricted_completed_square c f ha
    have hz : fineSize (f - (8 : ℝ) • normalizedLift c) = 0 := by linarith
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hz)
  · intro he
    have hs := unrestricted_completed_square c f ha
    rw [he, sub_self] at hs
    have hz : fineSize (0 : Edge → ℝ) = 0 := by simp [fineSize]
    rw [hz, add_zero, ← he] at hs
    exact hs

theorem corrected_norm_lower (c : physicalSpace) : 8 * size c.val ≤ fineSize (correctedLift c) := by
  rw [unrestricted_completed_square c.val (correctedLift c) (correctedLift_average c)]
  exact le_add_of_nonneg_right (fineSize_nonneg _)

def badSource : physicalSpace :=
  ⟨average PeriodicCoarseGaugeDiagnostics.badGradient,
    PeriodicCoarsePhysicalAveragingObstruction.averaged_bad_physical⟩

theorem bad_correction_strict : 512 < fineSize (correctedLift badSource) := by
  have hs : size badSource.val = 64 :=
    PeriodicCoarsePhysicalAveragingObstruction.averaged_bad_dot
  have hl := corrected_norm_lower badSource
  rw [hs] at hl
  apply lt_of_le_of_ne (by linarith : 512 ≤ fineSize (correctedLift badSource))
  intro he
  have he' : fineSize (correctedLift badSource) = 8 * size badSource.val := by
    rw [hs, ← he]
    norm_num
  have hf := (unrestricted_minimum_equality badSource.val (correctedLift badSource)
    (correctedLift_average badSource)).mp he'
  have hz := correctedLift_physical badSource PeriodicCoarseGaugeDiagnostics.badGradient
    PeriodicCoarseGaugeDiagnostics.badGradient_fine_closed
  rw [hf, smul_dotProduct] at hz
  change (8 : ℝ) • dotProduct
    (normalizedLift (average PeriodicCoarseGaugeDiagnostics.badGradient))
    PeriodicCoarseGaugeDiagnostics.badGradient = 0 at hz
  rw [PeriodicCoarsePhysicalAveragingObstruction.lift_gradient_coupling] at hz
  norm_num at hz

end OperatorDerivativeRewrite.Foundation.PeriodicPhysicalLiftMinimum
