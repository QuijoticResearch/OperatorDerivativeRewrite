import Foundation.PeriodicCheckerboardCompliance

/-! Equality of the actual norm and energy lifts is a fine Gram range condition. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicLiftEqualityCriterion
open PeriodicInteriorGaugeKernel PeriodicCoarseCurl PeriodicCoarsePhysicalSector
open PeriodicProjectedCoarseRange PeriodicCorrectedPhysicalLift
open PeriodicFinePhysicalGreen PeriodicEnergySchur PeriodicPhysicalEnergyMinimum
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

theorem A_B (c : physicalSpace) : A (B c) = physicalCompression c := rfl

theorem normLift_B (c : physicalSpace) : normLift c = B (multiplier c) := rfl

theorem normLift_compression (c : physicalSpace) :
    normLift (physicalCompression c) = B c := by
  rw [normLift_B]
  have h : multiplier (physicalCompression c) = c := compressionEquiv.symm_apply_apply c
  rw [h]

theorem energy_stationary_iff (c : physicalSpace) (f : fineSpace) (ha : A f = c) :
    f = energyLift c ↔ physicalGram f ∈ LinearMap.range B := by
  constructor
  · intro h
    subst f
    exact ⟨energyMultiplier c, (Subtype.ext (energyLift_euler c)).symm⟩
  · rintro ⟨d,hd⟩
    have hf : f = Green (B d) := by
      apply physicalGram_injective
      exact hd.symm.trans (Subtype.ext (Green_equation (B d))).symm
    have hs : S d = c := by rw [S_apply, ← hf, ha]
    have hm : d = energyMultiplier c := by
      apply S_injective
      exact hs.trans (schurEquiv.apply_symm_apply c).symm
    rw [hf, hm]
    rfl

theorem norm_energy_iff (c : physicalSpace) :
    normLift c = energyLift c ↔ physicalGram (normLift c) ∈ LinearMap.range B :=
  energy_stationary_iff c (normLift c) (normLift_average c)

theorem energy_equality_iff (c : physicalSpace) :
    fineEnergy (correctedLift c) = fineEnergy (energyLift c).val ↔
      physicalGram (normLift c) ∈ LinearMap.range B :=
  (equality_with_norm_lift c).trans (norm_energy_iff c)

theorem eigen_norm_lift (c : physicalSpace) (r : ℝ)
    (he : physicalGram (normLift c) = r • normLift c) :
    normLift c = energyLift c := by
  apply (norm_energy_iff c).mpr
  refine ⟨r • multiplier c, ?_⟩
  rw [map_smul, ← normLift_B, he]

theorem all_equal_iff_invariant :
    (∀ c : physicalSpace, normLift c = energyLift c) ↔
      (∀ d : physicalSpace, physicalGram (B d) ∈ LinearMap.range B) := by
  constructor
  · intro h d
    have hd := (norm_energy_iff (physicalCompression d)).mp (h (physicalCompression d))
    rwa [normLift_compression] at hd
  · intro h c
    apply (norm_energy_iff c).mpr
    rw [normLift_B]
    exact h (multiplier c)

theorem strict_iff_range_failure (c : physicalSpace) :
    fineEnergy (energyLift c).val < fineEnergy (correctedLift c) ↔
      physicalGram (normLift c) ∉ LinearMap.range B := by
  have hle := energy_vs_norm_minimum c
  have he := energy_equality_iff c
  constructor
  · intro h hm
    have hh := he.mpr hm
    linarith
  · intro h
    by_contra hn
    have hh : fineEnergy (correctedLift c) = fineEnergy (energyLift c).val := by
      linarith
    exact h (he.mp hh)

theorem actual_range_not_invariant :
    ¬ ∀ d : physicalSpace, physicalGram (B d) ∈ LinearMap.range B := by
  intro h
  exact PeriodicStrictEnergyWitness.distinct_minimizers
    (all_equal_iff_invariant.mpr h PeriodicPhysicalLiftMinimum.badSource)

theorem explicit_range_escape :
    physicalGram (B (multiplier PeriodicPhysicalLiftMinimum.badSource)) ∉
      LinearMap.range B := by
  rw [← normLift_B]
  exact (strict_iff_range_failure _).mp PeriodicStrictEnergyWitness.strict_energy_comparison

end OperatorDerivativeRewrite.Foundation.PeriodicLiftEqualityCriterion
