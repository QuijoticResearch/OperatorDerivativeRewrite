import Foundation.PeriodicLiftEqualityCriterion

/-! The constrained fine energy gradient and an exact feasible descent step. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicConstrainedEnergyDescent
open PeriodicInteriorGaugeKernel PeriodicCoarseCurl PeriodicCoarsePhysicalSector
open PeriodicProjectedCoarseRange PeriodicCorrectedPhysicalLift
open PeriodicFinePhysicalGreen PeriodicEnergySchur PeriodicPhysicalEnergyMinimum
open PeriodicLiftEqualityCriterion
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def N : fineSpace →ₗ[ℝ] fineSpace := B.comp (multiplier.comp A)

theorem N_apply (f : fineSpace) : N f = normLift (A f) := rfl

theorem A_N (f : fineSpace) : A (N f) = A f := normLift_average (A f)

theorem N_B (c : physicalSpace) : N (B c) = B c := by
  rw [N_apply, A_B, normLift_compression]

theorem N_idempotent (f : fineSpace) : N (N f) = N f := by
  change N (B (multiplier (A f))) = _
  rw [N_B]
  rfl

theorem fixed_iff_range (f : fineSpace) : N f = f ↔ f ∈ LinearMap.range B := by
  constructor
  · intro h
    exact ⟨multiplier (A f), h⟩
  · rintro ⟨c,rfl⟩
    exact N_B c

theorem kernel_pairing (v f : fineSpace) (hv : A v = 0) :
    dotProduct v.val (N f).val = 0 := by
  have h := adjunction v (multiplier (A f))
  rw [hv] at h
  exact h.trans (zero_dotProduct _)

def residual (f : fineSpace) : fineSpace := physicalGram f - N (physicalGram f)

theorem residual_average (f : fineSpace) : A (residual f) = 0 := by
  rw [residual, map_sub, A_N, sub_self]

theorem residual_zero_iff (f : fineSpace) : residual f = 0 ↔ f = energyLift (A f) := by
  rw [residual, sub_eq_zero, eq_comm, fixed_iff_range]
  exact (energy_stationary_iff (A f) f rfl).symm

theorem residual_pairing (f : fineSpace) :
    dotProduct (residual f).val (G f.val) =
      PeriodicPhysicalLiftMinimum.fineSize (residual f).val := by
  have ho := kernel_pairing (residual f) (physicalGram f) (residual_average f)
  have hd : (G f.val) = (residual f).val + (N (physicalGram f)).val := by
    change (physicalGram f).val = _
    simp only [residual, Submodule.coe_sub, sub_add_cancel]
  rw [hd, dotProduct_add, ho, add_zero]
  rfl

theorem feasible_step (f : fineSpace) (t : ℝ) :
    A (f - t • residual f) = A f := by
  rw [map_sub, map_smul, residual_average, smul_zero, sub_zero]

theorem energy_step (f : fineSpace) (t : ℝ) :
    fineEnergy (f - t • residual f).val = fineEnergy f.val +
      t^2 * fineEnergy (residual f).val -
      2*t*PeriodicPhysicalLiftMinimum.fineSize (residual f).val := by
  have h := energy_add ((-t) • (residual f).val) f.val
  rw [PeriodicStrictEnergyWitness.energy_smul, smul_dotProduct, residual_pairing] at h
  have hv : (f - t • residual f).val = (-t) • (residual f).val + f.val := by
    simp only [neg_smul, sub_eq_add_neg]
    exact add_comm _ _
  rw [hv, h]
  ring

theorem exact_descent (f : fineSpace) (hv : residual f ≠ 0) :
    let t := PeriodicPhysicalLiftMinimum.fineSize (residual f).val /
      fineEnergy (residual f).val
    fineEnergy (f - t • residual f).val = fineEnergy f.val -
      (PeriodicPhysicalLiftMinimum.fineSize (residual f).val)^2 /
        fineEnergy (residual f).val := by
  dsimp only
  rw [energy_step]
  have he := physical_energy_positive (residual f) hv
  field_simp [ne_of_gt he]
  ring

theorem strict_descent (f : fineSpace) (hv : residual f ≠ 0) :
    let t := PeriodicPhysicalLiftMinimum.fineSize (residual f).val /
      fineEnergy (residual f).val
    fineEnergy (f - t • residual f).val < fineEnergy f.val := by
  dsimp only
  rw [exact_descent f hv]
  have he := physical_energy_positive (residual f) hv
  have hn : PeriodicPhysicalLiftMinimum.fineSize (residual f).val ≠ 0 := by
    intro h
    exact hv (Subtype.ext (dotProduct_self_eq_zero.mp h))
  have hp := div_pos (sq_pos_of_ne_zero hn) he
  linarith

theorem norm_bad_residual_nonzero :
    residual (normLift PeriodicPhysicalLiftMinimum.badSource) ≠ 0 := by
  intro h
  have he := (residual_zero_iff _).mp h
  rw [normLift_average] at he
  exact PeriodicStrictEnergyWitness.distinct_minimizers he

theorem Gram_N_not_commute : physicalGram.comp N ≠ N.comp physicalGram := by
  intro h
  have he := congrArg (fun T : fineSpace →ₗ[ℝ] fineSpace =>
    T (B (multiplier PeriodicPhysicalLiftMinimum.badSource))) h
  simp only [LinearMap.comp_apply, N_B] at he
  have hr : physicalGram (B (multiplier PeriodicPhysicalLiftMinimum.badSource)) ∈
      LinearMap.range B := (fixed_iff_range _).mp he.symm
  exact explicit_range_escape hr

end OperatorDerivativeRewrite.Foundation.PeriodicConstrainedEnergyDescent
