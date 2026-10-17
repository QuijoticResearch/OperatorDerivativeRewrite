import Foundation.FiniteGammaRankOne

/-! The null quotient with exactly the manuscript inner product is already complete. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteGammaHilbertQuotient
open FiniteGammaSeed FiniteGammaTensor
open scoped TensorProduct
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def scale : ℝ := (Real.sqrt 3)⁻¹

theorem scale_pos : 0 < scale := inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))

theorem scale_ne_zero : scale ≠ 0 := ne_of_gt scale_pos

theorem scale_sq : scale * scale = (1/3 : ℝ) := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  unfold scale
  rw [← mul_inv, ← pow_two, h]
  norm_num

def normalizedMap : Tensor →ₗ[ℝ] Form := scale • tensorMap

theorem normalizedMap_tmul (f u : Algebra) :
    normalizedMap (f ⊗ₜ[ℝ] u) = scale • singleForm f u := by
  simp only [normalizedMap, LinearMap.smul_apply, tensorMap_tmul]

theorem normalizedMap_surjective : Function.Surjective normalizedMap := by
  intro v
  refine ⟨synthesis (scale⁻¹ • v), ?_⟩
  simp only [normalizedMap, LinearMap.smul_apply, tensorMap_synthesis,
    smul_smul, mul_inv_cancel₀ scale_ne_zero, one_smul]

def pairing (x y : Tensor) : ℝ := inner ℝ (normalizedMap x) (normalizedMap y)

theorem pairing_tmul (f u g v : Algebra) :
    pairing (f ⊗ₜ[ℝ] u) (g ⊗ₜ[ℝ] v) =
      expect (fun s => u s * v s * gamma f g s) := by
  rw [pairing, normalizedMap_tmul, normalizedMap_tmul,
    real_inner_smul_left, real_inner_smul_right, ← mul_assoc, scale_sq]
  exact pure_pairing f u g v

theorem finite_sum_pairing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f u : ι → Algebra) (g v : κ → Algebra) :
    pairing (∑ i, f i ⊗ₜ[ℝ] u i) (∑ j, g j ⊗ₜ[ℝ] v j) =
      ∑ i, ∑ j, expect (fun s => u i s * v j s * gamma (f i) (g j) s) := by
  unfold pairing
  simp only [map_sum, sum_inner, inner_sum]
  rw [Finset.sum_comm]
  change (∑ i, ∑ j, pairing (f i ⊗ₜ[ℝ] u i) (g j ⊗ₜ[ℝ] v j)) = _
  simp only [pairing_tmul]

abbrev Null := LinearMap.ker normalizedMap
abbrev EnergyQuotient := Tensor ⧸ Null

def realization : EnergyQuotient ≃ₗ[ℝ] Form :=
  normalizedMap.quotKerEquivOfSurjective normalizedMap_surjective

instance quotientNorm : NormedAddCommGroup EnergyQuotient :=
  NormedAddCommGroup.induced _ _ realization realization.injective

instance quotientNormedSpace : NormedSpace ℝ EnergyQuotient :=
  NormedSpace.induced ℝ _ _ realization

instance quotientInner : InnerProductSpace ℝ EnergyQuotient :=
  InnerProductSpace.induced realization

def hilbertEquiv : EnergyQuotient ≃ₗᵢ[ℝ] Form where
  toLinearEquiv := realization
  norm_map' _ := rfl

instance quotientComplete : CompleteSpace EnergyQuotient :=
  hilbertEquiv.toIsometryEquiv.completeSpace

theorem realization_mk (x : Tensor) :
    realization (Submodule.Quotient.mk x) = normalizedMap x :=
  normalizedMap.quotKerEquivOfSurjective_apply_mk _ _

theorem quotient_pairing (x y : Tensor) :
    inner ℝ (Submodule.Quotient.mk x : EnergyQuotient) (Submodule.Quotient.mk y) =
      pairing x y := by
  change inner ℝ (realization _) (realization _) = pairing x y
  rw [realization_mk, realization_mk]
  rfl

theorem null_iff_zero_energy (x : Tensor) : x ∈ Null ↔ pairing x x = 0 := by
  change normalizedMap x = 0 ↔ inner ℝ (normalizedMap x) (normalizedMap x) = 0
  exact (inner_self_eq_zero).symm

def singleClass (p : FiniteGammaSeed.Algebra × FiniteGammaSeed.Algebra) : EnergyQuotient :=
  Submodule.Quotient.mk (p.1 ⊗ₜ[ℝ] p.2)

theorem realized_single (p : FiniteGammaSeed.Algebra × FiniteGammaSeed.Algebra) :
    realization (singleClass p) = scale • singleForm p.1 p.2 := by
  rw [singleClass, realization_mk, normalizedMap_tmul]

end OperatorDerivativeRewrite.Foundation.FiniteGammaHilbertQuotient
