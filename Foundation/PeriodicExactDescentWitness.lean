import Foundation.PeriodicConstrainedEnergyDescent

/-! One feasible projected-gradient step attains the actual strict witness minimizer. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicExactDescentWitness
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarsePhysicalSector PeriodicCorrectedPhysicalLift PeriodicPhysicalLiftMinimum
open PeriodicFinePhysicalGreen PeriodicEnergySchur PeriodicPhysicalEnergyMinimum
open PeriodicConstrainedEnergyDescent PeriodicFineEnergyWitness PeriodicStrictEnergyWitness
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def j : fineSpace := normLift badSource

theorem j_value : j.val = (12 : ℝ) • p := norm_lift_source

theorem gram_j : (physicalGram j).val = (72 : ℝ) • p - (48 : ℝ) • a := by
  change G j.val = _
  rw [j_value, map_smul, gram_p]
  funext e
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem average_gram_j : A (physicalGram j) = (3 : ℝ) • badSource := by
  apply Subtype.ext
  change average (physicalGram j).val = (3 : ℝ) • c
  rw [gram_j, map_sub, map_smul, map_smul, average_p, average_a]
  funext e
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem projected_gram_j : (N (physicalGram j)).val = (36 : ℝ) • p := by
  rw [N_apply, average_gram_j]
  change correctedLift ((3 : ℝ) • badSource) = _
  rw [map_smul, norm_lift_source, smul_smul]
  norm_num

theorem residual_j : (residual j).val = (36 : ℝ) • p - (48 : ℝ) • a := by
  change (physicalGram j).val - (N (physicalGram j)).val = _
  rw [gram_j, projected_gram_j]
  funext e
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem one_step_exact : j - (1/5 : ℝ) • residual j = energyLift badSource := by
  apply Subtype.ext
  change j.val - (1/5 : ℝ) • (residual j).val = (energyLift badSource).val
  rw [j_value, residual_j, energy_lift_source, z]
  funext e
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem residual_j_size : fineSize (residual j).val = 2304 := by
  have h := residual_pairing j
  rw [residual_j] at h
  have hg : G j.val = (72 : ℝ) • p - (48 : ℝ) • a := gram_j
  rw [hg] at h
  have hpa : dotProduct p a = (4 : ℝ) := by
    have he := gram_energy p
    rw [gram_p, dotProduct_sub, dotProduct_smul, dotProduct_smul, p_energy] at he
    change 6 * fineSize p - 4 * dotProduct p a = 16 at he
    rw [p_size] at he
    linarith
  have haa : dotProduct a a = (4 : ℝ) := by
    have he := gram_symmetric p a
    rw [gram_a, gram_p, dotProduct_smul, sub_dotProduct,
      smul_dotProduct, smul_dotProduct, hpa] at he
    simp only [smul_eq_mul] at he
    linarith
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, dotProduct_comm a p, hpa, haa] at h
  change 72 * (36 * fineSize p - 48 * 4) - 48 * (36 * 4 - 48 * 4) =
    fineSize ((36 : ℝ) • p - (48 : ℝ) • a) at h
  rw [p_size] at h
  rw [residual_j]
  linarith

theorem residual_j_energy : fineEnergy (residual j).val = 11520 := by
  have h := energy_step j (1/5)
  rw [one_step_exact, energy_lift_energy, residual_j_size] at h
  have hj : fineEnergy j.val = 2304 := norm_lift_energy
  rw [hj] at h
  linarith

theorem optimal_step : fineSize (residual j).val / fineEnergy (residual j).val =
    (1/5 : ℝ) := by
  rw [residual_j_size, residual_j_energy]
  norm_num

end OperatorDerivativeRewrite.Foundation.PeriodicExactDescentWitness
