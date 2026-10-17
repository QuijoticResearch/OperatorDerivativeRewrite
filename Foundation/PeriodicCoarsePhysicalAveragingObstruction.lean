import Foundation.PeriodicCoarsePhysicalSector
import Foundation.PeriodicCoarseConstraint

/-! The averaging obstruction persists for an actual positive coarse physical eigenfield. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarsePhysicalAveragingObstruction
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseGaugeDiagnostics PeriodicCoarseEnergy PeriodicCoarseConstraint
open PeriodicCoarseWalshBasis PeriodicCoarseGramAction PeriodicCoarseEigenbasis
open PeriodicCoarsePhysicalSector
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def witnessLabel : Label := ({1},0)
theorem witness_eigenvalue : eigenvalue witnessLabel = 4 := by decide
theorem witness_mode : eigenMode witnessLabel = mode witnessLabel := by
  simp [eigenMode, witnessLabel]

theorem int_averaged_bad_mode : ∀ q : CoarseEdge,
    averageZ (gradient badPotentialZ) q = 16 * modeZ witnessLabel q := by decide

theorem averaged_bad_formula : average badGradient = (2 : ℝ) • mode witnessLabel := by
  have hb : badGradient = fun e => (gradient badPotentialZ e : ℝ) := funext badGradient_cast
  rw [hb]
  funext q
  rw [average_cast, int_averaged_bad_mode]
  simp only [Int.cast_mul, Int.cast_ofNat, Pi.smul_apply, smul_eq_mul, mode]
  ring

theorem averaged_bad_physical : average badGradient ∈ physicalSpace := by
  rw [averaged_bad_formula, ← witness_mode]
  apply Submodule.smul_mem
  exact positiveMode_physical witnessLabel (by rw [witness_eigenvalue]; norm_num)

theorem averaged_bad_eigen : H (average badGradient) = (4 : ℝ) • average badGradient := by
  rw [averaged_bad_formula, ← witness_mode, map_smul, mode_eigen, witness_eigenvalue]
  norm_num [smul_smul]

theorem averaged_bad_dot : dotProduct (average badGradient) (average badGradient) = 64 := by
  rw [averaged_bad_formula, smul_dotProduct, dotProduct_smul, mode_pair]
  norm_num [smul_eq_mul]

theorem H_energy (f : Field) : dotProduct f (H f) = coarseEnergy f := by
  rw [H_apply, gramMatrix, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
    PeriodicCoarseGramAction.incidenceMatrix_mulVec]
  simp [dotProduct, coarseEnergy, pow_two]

theorem averaged_bad_energy : coarseEnergy (average badGradient) = 256 := by
  rw [← H_energy, averaged_bad_eigen, dotProduct_smul, averaged_bad_dot]
  norm_num [smul_eq_mul]

theorem lifted_bad_energy : fineEnergy (normalizedLift (average badGradient)) = 16 := by
  rw [PeriodicCoarseEnergy.normalized_lift_energy, averaged_bad_energy]
  norm_num

theorem lift_gradient_coupling :
    dotProduct (normalizedLift (average badGradient)) badGradient = 64 := by
  rw [dotProduct_comm, lift_is_adjoint, averaged_bad_dot]

theorem lift_not_closed_orthogonal : ¬ ∀ (c : Field), c ∈ physicalSpace →
    ∀ g : Edge → ℝ, incidence g = 0 → dotProduct (normalizedLift c) g = 0 := by
  intro h
  have he := h (average badGradient) averaged_bad_physical badGradient badGradient_fine_closed
  rw [lift_gradient_coupling] at he
  norm_num at he

theorem zero_energy_fiber_physical : ∃ c : Field, c ∈ physicalSpace ∧
    ∃ f : Edge → ℝ, average f = c ∧ fineEnergy f = 0 ∧
      fineEnergy (normalizedLift c) = 16 :=
  ⟨average badGradient, averaged_bad_physical, badGradient, rfl,
    bad_fine_energy_zero, lifted_bad_energy⟩

end OperatorDerivativeRewrite.Foundation.PeriodicCoarsePhysicalAveragingObstruction
