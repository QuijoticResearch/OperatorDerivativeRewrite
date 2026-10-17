import Foundation.PeriodicEnergySchur

/-! Exact global curl-energy minimizer among fine physical preimages of a coarse field. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicPhysicalEnergyMinimum
open PeriodicInteriorGaugeKernel PeriodicCoarseCurl PeriodicCoarsePhysicalSector
open PeriodicCorrectedPhysicalLift PeriodicFinePhysicalGreen PeriodicEnergySchur
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

theorem energy_add (f g : Edge → ℝ) :
    fineEnergy (f + g) = fineEnergy f + fineEnergy g + 2 * dotProduct f (G g) := by
  have hc : dotProduct g (G f) = dotProduct f (G g) := by
    rw [dotProduct_comm g]
    exact (gram_symmetric f g).symm
  simp only [← gram_energy, map_add, add_dotProduct, dotProduct_add, hc]
  ring

theorem residual_orthogonal (c : physicalSpace) (f : fineSpace) (ha : A f = c) :
    dotProduct (f.val - (energyLift c).val) (G (energyLift c).val) = 0 := by
  have hav : A (f - energyLift c) = 0 := by
    rw [map_sub, ha, energyLift_average, sub_self]
  have h := adjunction (f - energyLift c) (energyMultiplier c)
  rw [hav] at h
  change dotProduct (f.val - (energyLift c).val) (B (energyMultiplier c)).val =
    dotProduct 0 (energyMultiplier c).val at h
  rw [zero_dotProduct] at h
  rw [energyLift_euler]
  exact h

theorem energy_completed_square (c : physicalSpace) (f : fineSpace) (ha : A f = c) :
    fineEnergy f.val = fineEnergy (energyLift c).val + fineEnergy (f - energyLift c).val := by
  have h := energy_add (f.val - (energyLift c).val) (energyLift c).val
  rw [sub_add_cancel, residual_orthogonal c f ha] at h
  change fineEnergy f.val = fineEnergy (energyLift c).val +
    fineEnergy (f.val - (energyLift c).val)
  linarith

theorem energy_minimum (c : physicalSpace) (f : fineSpace) (ha : A f = c) :
    fineEnergy (energyLift c).val ≤ fineEnergy f.val := by
  rw [energy_completed_square c f ha]
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem energy_minimum_unique (c : physicalSpace) (f : fineSpace) (ha : A f = c) :
    fineEnergy f.val = fineEnergy (energyLift c).val ↔ f = energyLift c := by
  constructor
  · intro he
    have hs := energy_completed_square c f ha
    have hz : fineEnergy (f - energyLift c).val = 0 := by linarith
    exact sub_eq_zero.mp ((physical_energy_zero_iff _).mp hz)
  · intro h
    rw [h]

theorem minimum_value_lower (c : physicalSpace) (f : fineSpace) (ha : A f = c) :
    dotProduct c.val (energyMultiplier c).val ≤ fineEnergy f.val := by
  rw [← energyLift_value]
  exact energy_minimum c f ha

theorem attained_value_positive (c : physicalSpace) (hc : c ≠ 0) :
    0 < dotProduct c.val (energyMultiplier c).val := by
  rw [← energyLift_value]
  apply physical_energy_positive
  intro he
  have ha := energyLift_average c
  rw [he, map_zero] at ha
  exact hc ha.symm

def normLift (c : physicalSpace) : fineSpace :=
  ⟨correctedLift c, correctedLift_physical c⟩

theorem normLift_average (c : physicalSpace) : A (normLift c) = c :=
  Subtype.ext (correctedLift_average c)

theorem energy_vs_norm_minimum (c : physicalSpace) :
    fineEnergy (energyLift c).val ≤ fineEnergy (correctedLift c) :=
  energy_minimum c (normLift c) (normLift_average c)

theorem equality_with_norm_lift (c : physicalSpace) :
    fineEnergy (correctedLift c) = fineEnergy (energyLift c).val ↔
      normLift c = energyLift c :=
  energy_minimum_unique c (normLift c) (normLift_average c)

end OperatorDerivativeRewrite.Foundation.PeriodicPhysicalEnergyMinimum
