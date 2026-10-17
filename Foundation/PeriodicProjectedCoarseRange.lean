import Foundation.PeriodicProjectedCoarseGram

/-! Exact closed kernel and physical range of the actual projected coarse Gram. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicProjectedCoarseRange
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseWalshBasis PeriodicCoarsePhysicalSector PeriodicCoarsePhysicalBounds
open PeriodicFinePhysicalProjection PeriodicProjectedCoarseLift PeriodicProjectedCoarseGram
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

theorem coarseEnergy_zero_iff (c : CoarseEdge → ℝ) :
    PeriodicCoarseEnergy.coarseEnergy c = 0 ↔ coarseIncidence c = 0 := by
  have he : PeriodicCoarseEnergy.coarseEnergy c =
      dotProduct (coarseIncidence c) (coarseIncidence c) := by
    simp [PeriodicCoarseEnergy.coarseEnergy, dotProduct, pow_two]
  rw [he]
  exact dotProduct_self_eq_zero

theorem fineEnergy_zero_iff (f : Edge → ℝ) : fineEnergy f = 0 ↔ incidence f = 0 := by
  have he : fineEnergy f = dotProduct (incidence f) (incidence f) := by
    simp [fineEnergy, dotProduct, pow_two]
  rw [he]
  exact dotProduct_self_eq_zero

theorem projectedLift_zero_iff (c : CoarseEdge → ℝ) :
    projectedLift c = 0 ↔ coarseIncidence c = 0 := by
  constructor
  · intro hz
    have h : fineEnergy (projectedLift c) = 0 := by rw [hz]; simp [fineEnergy]
    rw [projectedLift_energy] at h
    apply (coarseEnergy_zero_iff c).mp
    linarith
  · intro hc
    have he := (coarseEnergy_zero_iff c).mpr hc
    have hf : fineEnergy (projectedLift c) = 0 := by rw [projectedLift_energy, he, mul_zero]
    have hz := (fineEnergy_zero_iff _).mp hf
    exact dotProduct_self_eq_zero.mp (projectedLift_physical c _ hz)

theorem compression_zero_iff (c : CoarseEdge → ℝ) :
    compression c = 0 ↔ coarseIncidence c = 0 := by
  constructor
  · intro h
    have hn := compression_quadratic c
    rw [h, dotProduct_zero] at hn
    have hp : project (hilbertLift c) = 0 := by
      have hsq : ‖project (hilbertLift c)‖^2 = 0 := hn.symm
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (project (hilbertLift c))]
    apply (projectedLift_zero_iff c).mp
    rw [projectedLift_apply, hp, map_zero]
  · intro h
    change average (projectedLift c) = 0
    rw [(projectedLift_zero_iff c).mpr h, map_zero]

theorem compression_kernel : LinearMap.ker compression = LinearMap.ker coarseIncidence := by
  ext c
  exact compression_zero_iff c

theorem projectedLift_kernel : LinearMap.ker projectedLift = LinearMap.ker coarseIncidence := by
  ext c
  exact projectedLift_zero_iff c

theorem compression_mem_physical (c : CoarseEdge → ℝ) : compression c ∈ physicalSpace := by
  intro g hg
  rw [← compression_symmetric, (compression_zero_iff g).mpr hg, dotProduct_zero]

def physicalCompression : physicalSpace →ₗ[ℝ] physicalSpace where
  toFun c := ⟨compression c.val, compression_mem_physical c.val⟩
  map_add' c d := by apply Subtype.ext; exact map_add compression c.val d.val
  map_smul' r c := by apply Subtype.ext; exact map_smul compression r c.val

theorem physicalCompression_injective : Function.Injective physicalCompression := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro c hc
    have hz : compression c.val = 0 := congrArg Subtype.val hc
    have hclosed := (compression_zero_iff c.val).mp hz
    have hself := c.property c.val hclosed
    have he : c.val = 0 := dotProduct_self_eq_zero.mp hself
    rw [Submodule.mem_bot]
    exact Subtype.ext he
  · exact bot_le

def compressionEquiv : physicalSpace ≃ₗ[ℝ] physicalSpace :=
  LinearEquiv.ofInjectiveEndo physicalCompression physicalCompression_injective

theorem compression_range : LinearMap.range compression = physicalSpace := by
  apply le_antisymm
  · rintro _ ⟨c,rfl⟩
    exact compression_mem_physical c
  · intro c hc
    obtain ⟨u,hu⟩ := compressionEquiv.surjective ⟨c,hc⟩
    exact ⟨u.val, congrArg Subtype.val hu⟩

end OperatorDerivativeRewrite.Foundation.PeriodicProjectedCoarseRange
