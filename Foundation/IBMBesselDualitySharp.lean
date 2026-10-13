import Foundation.IBMBesselDuality

/-! Sharp Hilbert duality for the weighted-L² H⁻¹–H¹ pairing. -/
noncomputable section
open MeasureTheory
open scoped BesselPotentialSpace

namespace OperatorDerivativeRewrite.Foundation.IBMBesselDualitySharp
open IBMBesselDuality

/-- The weighted-L² H⁻¹ action on H¹ has exactly the H⁻¹ norm. -/
theorem pairingCLM_norm_eq (u : HminusOne) : ‖pairingCLM u‖ = ‖u‖ := by
  let v : HplusOne := (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (1 : ℝ) 2).symm u.toLp
  have hv : ‖v‖ = ‖u‖ := by simp [v, ← BesselPotentialSpace.norm_toLp_eq]
  have hval : pairingCLM u v = inner ℂ u.toLp u.toLp := by
    change inner ℂ u.toLp ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (1 : ℝ) 2) v) = _
    simp [v]
  apply le_antisymm (pairingCLM_norm_le u)
  by_cases hu : u = 0
  · simp [hu]
  have hle := (pairingCLM u).le_opNorm v
  have hvalnorm : ‖pairingCLM u v‖ = ‖u‖ * ‖u‖ := by
    rw [hval, inner_self_eq_norm_sq_to_K]
    simp [pow_two, ← BesselPotentialSpace.norm_toLp_eq]
  rw [hvalnorm, hv] at hle
  exact le_of_mul_le_mul_right hle (norm_pos_iff.mpr hu)

/-- Every continuous H¹ functional is represented by a unique H⁻¹ vector
through the weighted-L² pairing. -/
theorem pairingCLM_existsUnique (ℓ : HplusOne →L[ℂ] ℂ) :
    ∃! u : HminusOne, pairingCLM u = ℓ := by
  let T := BesselPotentialSpace.toLpₗᵢ ℝ ℂ (1 : ℝ) 2
  let lLp : (Lp ℂ 2 (MeasureTheory.volume : Measure ℝ)) →L[ℂ] ℂ :=
    ℓ.comp T.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let w := (InnerProductSpace.toDual ℂ (Lp ℂ 2 (MeasureTheory.volume : Measure ℝ))).symm lLp
  let u : HminusOne := (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).symm w
  have hsource : u.toLp = w := by
    change (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2)
      ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).symm w) = w
    simp
  have hex : pairingCLM u = ℓ := by
    apply ContinuousLinearMap.ext
    intro v
    change inner ℂ u.toLp v.toLp = ℓ v
    have hw := InnerProductSpace.toDual_symm_apply (x := v.toLp) (y := lLp)
    change inner ℂ w v.toLp = lLp v.toLp at hw
    rw [hsource, hw]
    change ℓ (T.symm (T v)) = ℓ v
    simp
  refine ⟨u, hex, ?_⟩
  intro u' hu'
  have hpair : ∀ v : HplusOne, pairing u' v = pairing u v := by
    intro v
    have heq := congrArg (fun L : HplusOne →L[ℂ] ℂ => L v) (hu'.trans hex.symm)
    exact heq
  have hz : u' - u = 0 := pairing_left_separating (u' - u) (by
    intro v
    change inner ℂ (u' - u).toLp v.toLp = 0
    change inner ℂ ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2) (u' - u)) v.toLp = 0
    rw [map_sub, inner_sub_left, sub_eq_zero]
    exact hpair v)
  exact sub_eq_zero.mp hz

end OperatorDerivativeRewrite.Foundation.IBMBesselDualitySharp
