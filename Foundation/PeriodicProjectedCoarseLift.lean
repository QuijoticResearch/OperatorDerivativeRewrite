import Foundation.PeriodicFinePhysicalProjection

/-! The actual projected transpose lift preserves energy but generally changes averaging. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicProjectedCoarseLift
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseWalshBasis PeriodicCoarsePhysicalSector PeriodicCoarsePhysicalBounds
open PeriodicFinePhysicalProjection
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def hilbertLift : (CoarseEdge → ℝ) →ₗ[ℝ] Fine :=
  raw.symm.toLinearMap.comp normalizedLift

def projectedLift : (CoarseEdge → ℝ) →ₗ[ℝ] (Edge → ℝ) :=
  raw.toLinearMap.comp (project.toLinearMap.comp hilbertLift)

theorem projectedLift_apply (c : CoarseEdge → ℝ) :
    projectedLift c = raw (project (hilbertLift c)) := rfl

theorem raw_hilbertLift (c : CoarseEdge → ℝ) : raw (hilbertLift c) = normalizedLift c :=
  raw.apply_symm_apply _

theorem projectedLift_physical (c : CoarseEdge → ℝ) (g : Edge → ℝ)
    (hg : incidence g = 0) : dotProduct (projectedLift c) g = 0 :=
  (physical_iff _).mp (project_mem _) g hg

theorem projectedLift_incidence (c : CoarseEdge → ℝ) :
    incidence (projectedLift c) = incidence (normalizedLift c) := by
  rw [projectedLift_apply, project_incidence, raw_hilbertLift]

theorem projectedLift_energy (c : CoarseEdge → ℝ) :
    fineEnergy (projectedLift c) = (1/16 : ℝ) * PeriodicCoarseEnergy.coarseEnergy c := by
  rw [projectedLift_apply, project_energy, raw_hilbertLift,
    PeriodicCoarseEnergy.normalized_lift_energy]

theorem projectedLift_bounds {c : CoarseEdge → ℝ} (hc : c ∈ physicalSpace) :
    (1/4 : ℝ) * size c ≤ fineEnergy (projectedLift c) ∧
      fineEnergy (projectedLift c) ≤ size c := by
  rw [projectedLift_energy]
  have hl := physical_coercive hc
  have hu := physical_upper hc
  constructor <;> linarith

theorem average_preserved_iff (c : CoarseEdge → ℝ) :
    average (projectedLift c) = (1/8 : ℝ) • c ↔ hilbertLift c ∈ physical := by
  constructor
  · intro ha
    let x := hilbertLift c
    let d := x - project x
    have hd : d ∈ closed := project_difference_closed x
    have hav : average (raw d) = 0 := by
      change average (raw (hilbertLift c - project (hilbertLift c))) = 0
      rw [map_sub, map_sub, raw_hilbertLift, average_normalizedLift]
      change (1/8 : ℝ) • c - average (projectedLift c) = 0
      rw [ha, sub_self]
    have hi : inner ℝ d x = 0 := by
      rw [inner_raw]
      change dotProduct (raw d) (raw (hilbertLift c)) = 0
      rw [raw_hilbertLift, lift_is_adjoint, hav, zero_dotProduct]
    have hp : inner ℝ d (project x) = 0 :=
      closed.inner_right_of_mem_orthogonal hd (project_mem x)
    have hz : d = 0 := inner_self_eq_zero.mp (by
      change inner ℝ d (x - project x) = 0
      rw [inner_sub_right, hi, hp, sub_zero])
    have hx : x = project x := sub_eq_zero.mp hz
    change x ∈ physical
    rw [hx]
    exact project_mem x
  · intro hc
    rw [projectedLift_apply, project_eq_self hc, raw_hilbertLift, average_normalizedLift]

theorem badLift_not_physical :
    hilbertLift (average PeriodicCoarseGaugeDiagnostics.badGradient) ∉ physical := by
  intro h
  have hz := (physical_iff _).mp h PeriodicCoarseGaugeDiagnostics.badGradient
    PeriodicCoarseGaugeDiagnostics.badGradient_fine_closed
  rw [raw_hilbertLift, PeriodicCoarsePhysicalAveragingObstruction.lift_gradient_coupling] at hz
  norm_num at hz

theorem projection_changes_average :
    average (projectedLift (average PeriodicCoarseGaugeDiagnostics.badGradient)) ≠
      (1/8 : ℝ) • average PeriodicCoarseGaugeDiagnostics.badGradient :=
  fun h => badLift_not_physical ((average_preserved_iff _).mp h)

theorem projected_bad_energy :
    fineEnergy (projectedLift (average PeriodicCoarseGaugeDiagnostics.badGradient)) = 16 := by
  rw [projectedLift_energy, PeriodicCoarsePhysicalAveragingObstruction.averaged_bad_energy]
  norm_num

theorem projected_norm_strict :
    ‖project (hilbertLift (average PeriodicCoarseGaugeDiagnostics.badGradient))‖ <
      ‖hilbertLift (average PeriodicCoarseGaugeDiagnostics.badGradient)‖ := by
  apply lt_of_le_of_ne (project_norm_le _)
  intro he
  exact badLift_not_physical ((physical.mem_iff_norm_starProjection _).mpr he)

end OperatorDerivativeRewrite.Foundation.PeriodicProjectedCoarseLift
