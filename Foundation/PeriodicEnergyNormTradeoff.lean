import Foundation.PeriodicStrictEnergyWitness

/-! Exact squared-norm increase accompanying the strict curl-energy decrease. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicEnergyNormTradeoff
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicFinePhysicalGreen PeriodicEnergySchur PeriodicPhysicalLiftMinimum
open PeriodicFineEnergyWitnessCertificates PeriodicFineEnergyWitness PeriodicStrictEnergyWitness
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 16000000 in
-- Kernel arithmetic computes the integer norm over all 1024 fine edges.
theorem a_int_size : (∑ e : Edge, aZ e * aZ e) = (256 : ℤ) := by decide

theorem a_size : fineSize a = 4 := by
  have he : dotProduct (fun e => (aZ e : ℝ)) (fun e => (aZ e : ℝ)) = 256 := by
    unfold dotProduct
    change (∑ e : Edge, (aZ e : ℝ) * (aZ e : ℝ)) = 256
    exact_mod_cast a_int_size
  rw [a]
  change dotProduct ((1/8 : ℝ) • (fun e => (aZ e : ℝ)))
    ((1/8 : ℝ) • (fun e => (aZ e : ℝ))) = 4
  rw [smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [he]
  norm_num

theorem a_physical : a ∈ fineSpace := by
  have h := fineSpace.smul_mem (1/2 : ℝ) (gram_mem_physical a)
  rw [gram_a, smul_smul] at h
  norm_num at h
  exact h

theorem a_p_pairing : dotProduct a p = 4 := by
  have h := PeriodicCorrectedPhysicalLift.projected_adjoint c a a_physical
  rw [projectedLift_formula, average_a, smul_dotProduct] at h
  change dotProduct a p = (1/16 : ℝ) * PeriodicCoarsePhysicalBounds.size c at h
  rw [source_size] at h
  linarith

theorem z_size : fineSize z = (28/27 : ℝ) := by
  have hp := p_size
  have ha := a_size
  change dotProduct p p = (16/3 : ℝ) at hp
  change dotProduct a a = 4 at ha
  unfold fineSize z
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  simp only [hp, ha, dotProduct_comm p a, a_p_pairing]
  norm_num

theorem fineSize_smul (r : ℝ) (f : Edge → ℝ) : fineSize (r • f) = r^2 * fineSize f := by
  unfold fineSize
  rw [smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

theorem energy_lift_size : fineSize (energyLift badSource).val = (21504/25 : ℝ) := by
  rw [energy_lift_source, fineSize_smul, z_size]
  norm_num

theorem strict_norm_comparison :
    fineSize (PeriodicCorrectedPhysicalLift.correctedLift badSource) <
      fineSize (energyLift badSource).val := by
  rw [norm_lift_size, energy_lift_size]
  norm_num

theorem energy_decrease :
    fineEnergy (PeriodicCorrectedPhysicalLift.correctedLift badSource) -
      fineEnergy (energyLift badSource).val = (2304/5 : ℝ) := by
  rw [norm_lift_energy, energy_lift_energy]
  norm_num

theorem squared_norm_increase :
    fineSize (energyLift badSource).val -
      fineSize (PeriodicCorrectedPhysicalLift.correctedLift badSource) = (2304/25 : ℝ) := by
  rw [energy_lift_size, norm_lift_size]
  norm_num

end OperatorDerivativeRewrite.Foundation.PeriodicEnergyNormTradeoff
