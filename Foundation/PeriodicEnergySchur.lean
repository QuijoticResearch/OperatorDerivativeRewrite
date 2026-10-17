import Foundation.PeriodicFinePhysicalGreen

/-! Actual coarse compliance operator using the inverse fine physical curl Gram. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicEnergySchur
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarsePhysicalSector PeriodicProjectedCoarseLift PeriodicProjectedCoarseRange
open PeriodicCorrectedPhysicalLift PeriodicFinePhysicalGreen
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def A : fineSpace →ₗ[ℝ] physicalSpace where
  toFun f := ⟨average f.val, average_physical f.val f.property⟩
  map_add' f g := by apply Subtype.ext; exact map_add average f.val g.val
  map_smul' r f := by apply Subtype.ext; exact map_smul average r f.val

def B : physicalSpace →ₗ[ℝ] fineSpace where
  toFun c := ⟨projectedLift c.val, projectedLift_physical c.val⟩
  map_add' c d := by apply Subtype.ext; exact map_add projectedLift c.val d.val
  map_smul' r c := by apply Subtype.ext; exact map_smul projectedLift r c.val

theorem adjunction (f : fineSpace) (c : physicalSpace) :
    dotProduct f.val (B c).val = dotProduct (A f).val c.val :=
  projected_adjoint c.val f.val f.property

theorem B_injective : Function.Injective B := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro c hc
    have hz : projectedLift c.val = 0 := congrArg Subtype.val hc
    have hk := (projectedLift_zero_iff c.val).mp hz
    have hs := c.property c.val hk
    rw [Submodule.mem_bot]
    exact Subtype.ext (dotProduct_self_eq_zero.mp hs)
  · exact bot_le

def S : physicalSpace →ₗ[ℝ] physicalSpace := A.comp (Green.comp B)

theorem S_apply (c : physicalSpace) : S c = A (Green (B c)) := rfl

theorem S_quadratic (c : physicalSpace) :
    dotProduct c.val (S c).val = dotProduct (B c).val (Green (B c)).val := by
  calc
    _ = dotProduct (S c).val c.val := dotProduct_comm _ _
    _ = dotProduct (Green (B c)).val (B c).val := (adjunction (Green (B c)) c).symm
    _ = _ := dotProduct_comm _ _

theorem S_symmetric (c d : physicalSpace) :
    dotProduct c.val (S d).val = dotProduct (S c).val d.val := by
  calc
    _ = dotProduct (S d).val c.val := dotProduct_comm _ _
    _ = dotProduct (Green (B d)).val (B c).val := (adjunction (Green (B d)) c).symm
    _ = dotProduct (B c).val (Green (B d)).val := dotProduct_comm _ _
    _ = dotProduct (Green (B c)).val (B d).val := (Green_symmetric (B c) (B d)).symm
    _ = _ := adjunction (Green (B c)) d

theorem S_positive (c : physicalSpace) (hc : c ≠ 0) :
    0 < dotProduct c.val (S c).val := by
  rw [S_quadratic]
  apply Green_positive
  intro h
  apply hc
  apply B_injective
  simpa only [map_zero] using h

theorem S_injective : Function.Injective S := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro c hc
    have hz : S c = 0 := hc
    have he : c = 0 := by
      by_contra hn
      have hp := S_positive c hn
      rw [hz] at hp
      change 0 < dotProduct c.val 0 at hp
      rw [dotProduct_zero] at hp
      exact (lt_irrefl _ hp)
    rw [Submodule.mem_bot]
    exact he
  · exact bot_le

def schurEquiv : physicalSpace ≃ₗ[ℝ] physicalSpace :=
  LinearEquiv.ofInjectiveEndo S S_injective

def energyMultiplier : physicalSpace →ₗ[ℝ] physicalSpace := schurEquiv.symm.toLinearMap

def energyLift : physicalSpace →ₗ[ℝ] fineSpace := Green.comp (B.comp energyMultiplier)

theorem energyLift_average (c : physicalSpace) : A (energyLift c) = c :=
  schurEquiv.apply_symm_apply c

theorem energyLift_euler (c : physicalSpace) :
    G (energyLift c).val = (B (energyMultiplier c)).val := Green_equation _

theorem energyLift_value (c : physicalSpace) :
    fineEnergy (energyLift c).val = dotProduct c.val (energyMultiplier c).val := by
  rw [← gram_energy, energyLift_euler]
  rw [adjunction, energyLift_average]

end OperatorDerivativeRewrite.Foundation.PeriodicEnergySchur
