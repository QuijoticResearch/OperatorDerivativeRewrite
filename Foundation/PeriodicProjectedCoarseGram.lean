import Foundation.PeriodicProjectedCoarseLift

/-! Positive projected coarse Gram form and strict loss of the raw scaled identity. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicProjectedCoarseGram
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseWalshBasis PeriodicCoarsePhysicalSector PeriodicCoarsePhysicalBounds
open PeriodicFinePhysicalProjection PeriodicProjectedCoarseLift
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def compression : (CoarseEdge → ℝ) →ₗ[ℝ] (CoarseEdge → ℝ) := average.comp projectedLift

theorem hilbertLift_norm_sq (c : CoarseEdge → ℝ) :
    ‖hilbertLift c‖^2 = (1/8 : ℝ) * size c := by
  rw [← real_inner_self_eq_norm_sq, inner_raw, raw_hilbertLift, lift_is_adjoint,
    average_normalizedLift, smul_dotProduct]
  rfl

theorem compression_quadratic (c : CoarseEdge → ℝ) :
    dotProduct c (compression c) = ‖project (hilbertLift c)‖^2 := by
  change dotProduct c (average (projectedLift c)) = _
  rw [dotProduct_comm c, ← lift_is_adjoint, projectedLift_apply,
    ← raw_hilbertLift, ← inner_raw]
  simpa only [RCLike.re_to_real, project, Submodule.starProjection_apply,
    Submodule.norm_coe] using
    physical.re_inner_starProjection_eq_normSq (hilbertLift c)

theorem compression_bilinear (c d : CoarseEdge → ℝ) :
    dotProduct c (compression d) = inner ℝ (hilbertLift c) (project (hilbertLift d)) := by
  change dotProduct c (average (projectedLift d)) = _
  rw [dotProduct_comm c, ← lift_is_adjoint, projectedLift_apply,
    ← raw_hilbertLift, ← inner_raw, real_inner_comm]

theorem compression_symmetric (c d : CoarseEdge → ℝ) :
    dotProduct c (compression d) = dotProduct (compression c) d := by
  rw [compression_bilinear, dotProduct_comm (compression c), compression_bilinear]
  change inner ℝ (hilbertLift c) (physical.starProjection (hilbertLift d)) =
    inner ℝ (hilbertLift d) (physical.starProjection (hilbertLift c))
  rw [← physical.inner_starProjection_left_eq_right]
  exact real_inner_comm _ _

theorem compression_nonneg (c : CoarseEdge → ℝ) : 0 ≤ dotProduct c (compression c) := by
  rw [compression_quadratic]
  exact sq_nonneg _

theorem compression_upper (c : CoarseEdge → ℝ) :
    dotProduct c (compression c) ≤ (1/8 : ℝ) * size c := by
  rw [compression_quadratic, ← hilbertLift_norm_sq]
  have h := project_norm_le (hilbertLift c)
  have hp := norm_nonneg (project (hilbertLift c))
  have hx := norm_nonneg (hilbertLift c)
  nlinarith

theorem projectedLift_nonzero {c : CoarseEdge → ℝ} (hc : c ∈ physicalSpace) (hn : c ≠ 0) :
    project (hilbertLift c) ≠ 0 := by
  intro hz
  have hl : projectedLift c = 0 := by
    rw [projectedLift_apply, hz, map_zero]
  have he : fineEnergy (projectedLift c) = 0 := by
    rw [hl]
    simp [fineEnergy]
  rw [projectedLift_energy] at he
  have hc' := physical_coercive hc
  have hs := size_nonneg c
  have hz' : size c = 0 := by linarith
  exact hn (dotProduct_self_eq_zero.mp hz')

theorem compression_positive {c : CoarseEdge → ℝ} (hc : c ∈ physicalSpace) (hn : c ≠ 0) :
    0 < dotProduct c (compression c) := by
  rw [compression_quadratic]
  exact sq_pos_of_pos (norm_pos_iff.mpr (projectedLift_nonzero hc hn))

theorem bad_compression_strict :
    dotProduct (average PeriodicCoarseGaugeDiagnostics.badGradient)
      (compression (average PeriodicCoarseGaugeDiagnostics.badGradient)) < 8 := by
  rw [compression_quadratic]
  have hp := projected_norm_strict
  have hn := norm_nonneg
    (project (hilbertLift (average PeriodicCoarseGaugeDiagnostics.badGradient)))
  have hx := hilbertLift_norm_sq (average PeriodicCoarseGaugeDiagnostics.badGradient)
  change ‖hilbertLift (average PeriodicCoarseGaugeDiagnostics.badGradient)‖^2 =
    (1/8 : ℝ) * dotProduct (average PeriodicCoarseGaugeDiagnostics.badGradient)
      (average PeriodicCoarseGaugeDiagnostics.badGradient) at hx
  rw [PeriodicCoarsePhysicalAveragingObstruction.averaged_bad_dot] at hx
  nlinarith

theorem compression_not_scaled_identity :
    ¬ ∀ c : CoarseEdge → ℝ, c ∈ physicalSpace → compression c = (1/8 : ℝ) • c := by
  intro h
  have he := h (average PeriodicCoarseGaugeDiagnostics.badGradient)
    PeriodicCoarsePhysicalAveragingObstruction.averaged_bad_physical
  have hs := bad_compression_strict
  rw [he, dotProduct_smul,
    PeriodicCoarsePhysicalAveragingObstruction.averaged_bad_dot] at hs
  norm_num [smul_eq_mul] at hs

end OperatorDerivativeRewrite.Foundation.PeriodicProjectedCoarseGram
