import Foundation.PeriodicProjectedCoarseRange

/-! The actual projected Gram inverse gives an exact physical right inverse of averaging. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCorrectedPhysicalLift
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseWalshBasis PeriodicCoarsePhysicalSector
open PeriodicFinePhysicalProjection PeriodicProjectedCoarseLift PeriodicProjectedCoarseGram
open PeriodicProjectedCoarseRange
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def multiplier : physicalSpace →ₗ[ℝ] physicalSpace := compressionEquiv.symm.toLinearMap

def correctedLift : physicalSpace →ₗ[ℝ] (Edge → ℝ) :=
  projectedLift.comp (physicalSpace.subtype.comp multiplier)

theorem compression_multiplier (c : physicalSpace) : compression (multiplier c).val = c.val :=
  congrArg Subtype.val (compressionEquiv.apply_symm_apply c)

theorem correctedLift_apply (c : physicalSpace) :
    correctedLift c = projectedLift (multiplier c).val := rfl

theorem correctedLift_average (c : physicalSpace) : average (correctedLift c) = c.val :=
  compression_multiplier c

theorem correctedLift_physical (c : physicalSpace) (g : Edge → ℝ)
    (hg : incidence g = 0) : dotProduct (correctedLift c) g = 0 :=
  projectedLift_physical (multiplier c).val g hg

theorem correctedLift_energy (c : physicalSpace) :
    fineEnergy (correctedLift c) =
      (1/16 : ℝ) * PeriodicCoarseEnergy.coarseEnergy (multiplier c).val :=
  projectedLift_energy _

theorem projected_adjoint (c : CoarseEdge → ℝ) (f : Edge → ℝ)
    (hf : ∀ g : Edge → ℝ, incidence g = 0 → dotProduct f g = 0) :
    dotProduct f (projectedLift c) = dotProduct (average f) c := by
  have hd := (closed_iff _).mp (project_difference_closed (hilbertLift c))
  have he := hf (raw (hilbertLift c - project (hilbertLift c))) hd
  rw [map_sub, raw_hilbertLift] at he
  change dotProduct f (normalizedLift c - projectedLift c) = 0 at he
  rw [dotProduct_sub] at he
  calc
    _ = dotProduct f (normalizedLift c) := (sub_eq_zero.mp he).symm
    _ = _ := lift_is_adjoint f c

theorem average_physical (f : Edge → ℝ)
    (hf : ∀ g : Edge → ℝ, incidence g = 0 → dotProduct f g = 0) :
    average f ∈ physicalSpace := by
  intro g hg
  rw [← projected_adjoint g f hf, (projectedLift_zero_iff g).mpr hg, dotProduct_zero]

theorem physical_preimage_iff (c : CoarseEdge → ℝ) :
    (∃ f : Edge → ℝ, average f = c ∧
      ∀ g : Edge → ℝ, incidence g = 0 → dotProduct f g = 0) ↔ c ∈ physicalSpace := by
  constructor
  · rintro ⟨f,hf,hp⟩
    rw [← hf]
    exact average_physical f hp
  · intro hc
    exact ⟨correctedLift ⟨c,hc⟩, correctedLift_average _, correctedLift_physical _⟩

theorem correctedLift_injective : Function.Injective correctedLift := by
  intro c d h
  apply Subtype.ext
  have he := congrArg (fun f => average f) h
  simpa only [correctedLift_average] using he

end OperatorDerivativeRewrite.Foundation.PeriodicCorrectedPhysicalLift
