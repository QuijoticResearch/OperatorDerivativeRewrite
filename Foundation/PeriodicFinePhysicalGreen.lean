import Foundation.PeriodicPhysicalLiftMinimum

/-! The actual fine curl Gram is invertible after removing its entire closed kernel. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicFinePhysicalGreen
open PeriodicInteriorGaugeKernel PeriodicCoarseCurl PeriodicProjectedCoarseRange
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def fineSpace : Submodule ℝ (Edge → ℝ) where
  carrier := {f | ∀ g : Edge → ℝ, incidence g = 0 → dotProduct f g = 0}
  zero_mem' := by intro g _; simp
  add_mem' := by intro f h hf hh g hg; simp [add_dotProduct, hf g hg, hh g hg]
  smul_mem' := by intro r f hf g hg; simp [smul_dotProduct, hf g hg]

def fullIncidenceMatrix : Matrix Face Edge ℝ := LinearMap.toMatrix' incidence

def fullGram : Matrix Edge Edge ℝ := fullIncidenceMatrix.transpose * fullIncidenceMatrix

def G : (Edge → ℝ) →ₗ[ℝ] (Edge → ℝ) := Matrix.toLin' fullGram

theorem fullIncidence_apply (f : Edge → ℝ) : fullIncidenceMatrix.mulVec f = incidence f :=
  LinearMap.toMatrix'_mulVec _ _

theorem gram_pairing (f g : Edge → ℝ) :
    dotProduct f (G g) = dotProduct (incidence f) (incidence g) := by
  change dotProduct f (fullGram.mulVec g) = _
  rw [fullGram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
    fullIncidence_apply, fullIncidence_apply]
  exact dotProduct_comm _ _

theorem gram_symmetric (f g : Edge → ℝ) : dotProduct f (G g) = dotProduct (G f) g := by
  rw [gram_pairing, dotProduct_comm (G f), gram_pairing, dotProduct_comm (incidence g)]

theorem gram_energy (f : Edge → ℝ) : dotProduct f (G f) = fineEnergy f := by
  rw [gram_pairing]
  simp [dotProduct, fineEnergy, pow_two]

theorem gram_mem_physical (f : Edge → ℝ) : G f ∈ fineSpace := by
  intro g hg
  rw [dotProduct_comm, gram_pairing, hg, zero_dotProduct]

theorem physical_energy_zero_iff (f : fineSpace) : fineEnergy f.val = 0 ↔ f = 0 := by
  constructor
  · intro he
    have hc := (fineEnergy_zero_iff f.val).mp he
    have hz := f.property f.val hc
    exact Subtype.ext (dotProduct_self_eq_zero.mp hz)
  · intro he
    rw [he]
    simp [fineEnergy]

theorem physical_energy_positive (f : fineSpace) (hf : f ≠ 0) : 0 < fineEnergy f.val := by
  have hn : fineEnergy f.val ≠ 0 := fun h => hf ((physical_energy_zero_iff f).mp h)
  exact lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Ne.symm hn)

def physicalGram : fineSpace →ₗ[ℝ] fineSpace where
  toFun f := ⟨G f.val, gram_mem_physical f.val⟩
  map_add' f g := by apply Subtype.ext; exact map_add G f.val g.val
  map_smul' r f := by apply Subtype.ext; exact map_smul G r f.val

theorem physicalGram_injective : Function.Injective physicalGram := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro f hf
    have hg : G f.val = 0 := congrArg Subtype.val hf
    have he : fineEnergy f.val = 0 := by rw [← gram_energy, hg, dotProduct_zero]
    rw [Submodule.mem_bot]
    exact (physical_energy_zero_iff f).mp he
  · exact bot_le

def greenEquiv : fineSpace ≃ₗ[ℝ] fineSpace :=
  LinearEquiv.ofInjectiveEndo physicalGram physicalGram_injective

def Green : fineSpace →ₗ[ℝ] fineSpace := greenEquiv.symm.toLinearMap

theorem Green_equation (f : fineSpace) : G (Green f).val = f.val :=
  congrArg Subtype.val (greenEquiv.apply_symm_apply f)

theorem Green_symmetric (f g : fineSpace) :
    dotProduct (Green f).val g.val = dotProduct f.val (Green g).val := by
  have h := gram_symmetric (Green f).val (Green g).val
  rw [Green_equation, Green_equation] at h
  exact h

theorem Green_energy (f : fineSpace) :
    fineEnergy (Green f).val = dotProduct (Green f).val f.val := by
  rw [← gram_energy, Green_equation]

theorem Green_nonzero (f : fineSpace) (hf : f ≠ 0) : Green f ≠ 0 := by
  intro h
  have he := Green_equation f
  rw [h] at he
  have hz : f.val = 0 := by simpa using he.symm
  exact hf (Subtype.ext hz)

theorem Green_positive (f : fineSpace) (hf : f ≠ 0) :
    0 < dotProduct f.val (Green f).val := by
  have h := physical_energy_positive (Green f) (Green_nonzero f hf)
  rw [Green_energy, dotProduct_comm] at h
  exact h

end OperatorDerivativeRewrite.Foundation.PeriodicFinePhysicalGreen
