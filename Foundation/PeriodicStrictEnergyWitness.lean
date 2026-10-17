import Foundation.PeriodicFineEnergyWitness

/-! A native strict comparison of the norm and curl-energy minimizers in the actual lattice. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicStrictEnergyWitness
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarsePhysicalSector PeriodicProjectedCoarseLift PeriodicProjectedCoarseRange
open PeriodicFinePhysicalGreen PeriodicEnergySchur PeriodicPhysicalEnergyMinimum
open PeriodicPhysicalLiftMinimum
open PeriodicFineEnergyWitness
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

theorem source_value : badSource.val = c := rfl

theorem source_size : PeriodicCoarsePhysicalBounds.size c = 64 :=
  PeriodicCoarsePhysicalAveragingObstruction.averaged_bad_dot

theorem B_source : B badSource = ⟨p,p_physical⟩ :=
  Subtype.ext projectedLift_formula

theorem Green_B_source : Green (B badSource) = ⟨z,z_physical⟩ := by
  apply physicalGram_injective
  apply Subtype.ext
  change G (Green (B badSource)).val = G z
  rw [Green_equation, B_source, gram_z]

theorem Q_source : physicalCompression badSource = (1/12 : ℝ) • badSource := by
  apply Subtype.ext
  change average (projectedLift c) = (1/12 : ℝ) • c
  rw [projectedLift_formula, average_p]

theorem S_source : S badSource = (5/144 : ℝ) • badSource := by
  rw [S_apply, Green_B_source]
  apply Subtype.ext
  exact average_z

theorem norm_multiplier_source :
    PeriodicCorrectedPhysicalLift.multiplier badSource = (12 : ℝ) • badSource := by
  apply physicalCompression_injective
  have he : physicalCompression (PeriodicCorrectedPhysicalLift.multiplier badSource) =
      badSource := compressionEquiv.apply_symm_apply badSource
  rw [he, map_smul, Q_source]
  norm_num [smul_smul]

theorem energy_multiplier_source :
    energyMultiplier badSource = (144/5 : ℝ) • badSource := by
  apply S_injective
  have he : S (energyMultiplier badSource) = badSource := schurEquiv.apply_symm_apply badSource
  rw [he, map_smul, S_source]
  norm_num [smul_smul]

theorem norm_lift_source : PeriodicCorrectedPhysicalLift.correctedLift badSource = (12 : ℝ) • p := by
  rw [PeriodicCorrectedPhysicalLift.correctedLift_apply, norm_multiplier_source]
  change projectedLift ((12 : ℝ) • c) = _
  rw [map_smul, projectedLift_formula]

theorem energy_lift_source : (energyLift badSource).val = (144/5 : ℝ) • z := by
  change (Green (B (energyMultiplier badSource))).val = _
  rw [energy_multiplier_source, map_smul, map_smul, Green_B_source]
  rfl

theorem p_energy : fineEnergy p = 16 := by
  rw [← projectedLift_formula]
  exact projected_bad_energy

theorem p_size : fineSize p = (16/3 : ℝ) := by
  have h := PeriodicCorrectedPhysicalLift.projected_adjoint c p p_physical
  rw [projectedLift_formula, average_p, smul_dotProduct] at h
  change fineSize p = (1/12 : ℝ) * PeriodicCoarsePhysicalBounds.size c at h
  rw [source_size] at h
  linarith

theorem z_pairing : dotProduct z p = (20/9 : ℝ) := by
  have h := PeriodicCorrectedPhysicalLift.projected_adjoint c z z_physical
  rw [projectedLift_formula, average_z, smul_dotProduct] at h
  change dotProduct z p = (5/144 : ℝ) * PeriodicCoarsePhysicalBounds.size c at h
  rw [source_size] at h
  linarith

theorem z_energy : fineEnergy z = (20/9 : ℝ) := by
  rw [← gram_energy, gram_z, z_pairing]

theorem energy_smul (r : ℝ) (f : Edge → ℝ) : fineEnergy (r • f) = r^2 * fineEnergy f := by
  rw [← gram_energy, map_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [gram_energy]
  ring

theorem norm_lift_energy :
    fineEnergy (PeriodicCorrectedPhysicalLift.correctedLift badSource) = 2304 := by
  rw [norm_lift_source, energy_smul, p_energy]
  norm_num

theorem energy_lift_energy : fineEnergy (energyLift badSource).val = (9216/5 : ℝ) := by
  rw [energy_lift_source, energy_smul, z_energy]
  norm_num

theorem strict_energy_comparison : fineEnergy (energyLift badSource).val <
    fineEnergy (PeriodicCorrectedPhysicalLift.correctedLift badSource) := by
  rw [energy_lift_energy, norm_lift_energy]
  norm_num

theorem distinct_minimizers : normLift badSource ≠ energyLift badSource := by
  intro h
  have he := congrArg (fun f : fineSpace => fineEnergy f.val) h
  have hs := strict_energy_comparison
  change fineEnergy (PeriodicCorrectedPhysicalLift.correctedLift badSource) =
    fineEnergy (energyLift badSource).val at he
  linarith

theorem norm_lift_size :
    fineSize (PeriodicCorrectedPhysicalLift.correctedLift badSource) = 768 := by
  rw [norm_lift_source]
  change dotProduct ((12 : ℝ) • p) ((12 : ℝ) • p) = 768
  rw [smul_dotProduct, dotProduct_smul]
  change 12 * (12 * fineSize p) = 768
  rw [p_size]
  norm_num

end OperatorDerivativeRewrite.Foundation.PeriodicStrictEnergyWitness
