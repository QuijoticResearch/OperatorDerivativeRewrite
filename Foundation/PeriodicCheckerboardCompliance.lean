import Foundation.PeriodicCheckerboardPhysical
import Foundation.PeriodicStrictEnergyWitness

/-! Exact compliance eigenvalues and coincident norm/energy minimizers on a checkerboard mode. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCheckerboardCompliance
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarsePhysicalSector PeriodicFinePhysicalProjection PeriodicProjectedCoarseLift
open PeriodicProjectedCoarseRange PeriodicFinePhysicalGreen PeriodicEnergySchur
open PeriodicCheckerboardPhysical
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def fineLift : fineSpace := ⟨lift,lift_physical⟩

theorem normalized_physical : normalizedLift source ∈ fineSpace := by
  rw [normalizedLift, LinearMap.smul_apply, ← lift_flat]
  exact fineSpace.smul_mem (1/8 : ℝ) lift_physical

theorem hilbertLift_physical : hilbertLift source ∈ physical := by
  apply (physical_iff _).mpr
  rw [raw_hilbertLift]
  exact normalized_physical

theorem projected_lift : projectedLift source = (1/8 : ℝ) • lift := by
  rw [projectedLift_apply, project_eq_self hilbertLift_physical, raw_hilbertLift,
    normalizedLift, LinearMap.smul_apply, ← lift_flat]

theorem B_checker : B physicalSource = (1/8 : ℝ) • fineLift :=
  Subtype.ext projected_lift

theorem A_fineLift : A fineLift = physicalSource := Subtype.ext average_lift

theorem Q_checker : physicalCompression physicalSource = (1/8 : ℝ) • physicalSource := by
  apply Subtype.ext
  change average (projectedLift source) = (1/8 : ℝ) • source
  rw [projected_lift, map_smul, average_lift]

theorem Green_fineLift : Green fineLift = (1/8 : ℝ) • fineLift := by
  apply physicalGram_injective
  apply Subtype.ext
  change G (Green fineLift).val = G ((1/8 : ℝ) • lift)
  rw [Green_equation, map_smul, gram_lift, smul_smul]
  norm_num [fineLift]

theorem Green_B_checker : Green (B physicalSource) = (1/64 : ℝ) • fineLift := by
  rw [B_checker, map_smul, Green_fineLift, smul_smul]
  norm_num

theorem S_checker : S physicalSource = (1/64 : ℝ) • physicalSource := by
  rw [S_apply, Green_B_checker, map_smul, A_fineLift]

theorem norm_multiplier :
    PeriodicCorrectedPhysicalLift.multiplier physicalSource = (8 : ℝ) • physicalSource := by
  apply physicalCompression_injective
  have he : physicalCompression (PeriodicCorrectedPhysicalLift.multiplier physicalSource) =
      physicalSource := compressionEquiv.apply_symm_apply physicalSource
  rw [he, map_smul, Q_checker, smul_smul]
  norm_num

theorem energy_multiplier : energyMultiplier physicalSource = (64 : ℝ) • physicalSource := by
  apply S_injective
  have he : S (energyMultiplier physicalSource) = physicalSource :=
    schurEquiv.apply_symm_apply physicalSource
  rw [he, map_smul, S_checker, smul_smul]
  norm_num

theorem norm_lift : PeriodicCorrectedPhysicalLift.correctedLift physicalSource = lift := by
  rw [PeriodicCorrectedPhysicalLift.correctedLift_apply, norm_multiplier]
  change projectedLift ((8 : ℝ) • source) = lift
  rw [map_smul, projected_lift, smul_smul]
  norm_num

theorem energy_lift : (energyLift physicalSource).val = lift := by
  change (Green (B (energyMultiplier physicalSource))).val = lift
  rw [energy_multiplier, map_smul, map_smul, Green_B_checker, smul_smul]
  norm_num [fineLift]

theorem same_minimizing_field : PeriodicCorrectedPhysicalLift.correctedLift physicalSource =
    (energyLift physicalSource).val := by rw [norm_lift, energy_lift]

theorem checker_energy : fineEnergy lift = 2048 := by
  rw [← gram_energy, gram_lift, dotProduct_smul]
  change 8 * PeriodicPhysicalLiftMinimum.fineSize lift = 2048
  rw [lift_size]
  norm_num

theorem compliance_not_scalar_compression :
    ¬ ∃ r : ℝ, S = r • physicalCompression := by
  rintro ⟨r,hr⟩
  have hn := congrArg (fun T : physicalSpace →ₗ[ℝ] physicalSpace => T physicalSource) hr
  simp only [S_checker, LinearMap.smul_apply, Q_checker, smul_smul] at hn
  have hnc := smul_left_injective ℝ physicalSource_nonzero hn
  have hbad : PeriodicPhysicalLiftMinimum.badSource ≠ 0 := by
    intro h
    have hv := congrArg Subtype.val h
    have hs := PeriodicStrictEnergyWitness.source_size
    change PeriodicCoarsePhysicalBounds.size PeriodicFineEnergyWitness.c = 64 at hs
    change PeriodicFineEnergyWitness.c = 0 at hv
    rw [hv] at hs
    norm_num [PeriodicCoarsePhysicalBounds.size] at hs
  have hb := congrArg (fun T : physicalSpace →ₗ[ℝ] physicalSpace =>
    T PeriodicPhysicalLiftMinimum.badSource) hr
  simp only [PeriodicStrictEnergyWitness.S_source, LinearMap.smul_apply,
    PeriodicStrictEnergyWitness.Q_source, smul_smul] at hb
  have hbc := smul_left_injective ℝ hbad hb
  nlinarith

end OperatorDerivativeRewrite.Foundation.PeriodicCheckerboardCompliance
