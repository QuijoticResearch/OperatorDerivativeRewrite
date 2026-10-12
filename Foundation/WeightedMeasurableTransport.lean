import Foundation.WeightedL2Transport
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

/-!
# Weighted L² transport on measurable subspaces

If the multiplier is measurable for a sub-sigma-algebra, the actual weighted
unitary restricts to Mathlib's `lpMeas` subspaces. Both directions follow from
measurability of multiplication and division, with the appropriate changes of
almost-everywhere relation. No filtration or stochastic integral is assumed.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace OperatorDerivativeRewrite.Foundation.WeightedMeasurableTransport

open WeightedL2Transport

variable {Ω : Type*} (m : MeasurableSpace Ω) {m₀ : MeasurableSpace Ω}
  (μ : Measure[m₀] Ω) (σ : Ω → ℝ) (hm : m ≤ m₀)
  (hσ : Measurable[m] σ) (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)

theorem aestronglyMeasurable_unitary
    {u : Lp ℝ 2 (weightedMeasure μ σ)}
    (hu : AEStronglyMeasurable[m] u (weightedMeasure μ σ)) :
    AEStronglyMeasurable[m] (unitary μ σ (hσ.mono hm le_rfl) hne u) μ := by
  have hsu : AEStronglyMeasurable[m] (fun ω => σ ω * u ω) μ :=
    hσ.stronglyMeasurable.aestronglyMeasurable.mul
      (hu.mono_ac (absolutelyContinuous_weightedMeasure μ σ (hσ.mono hm le_rfl) hne))
  exact hsu.congr (unitary_coeFn μ σ (hσ.mono hm le_rfl) hne u).symm

theorem aestronglyMeasurable_unitary_symm {v : Lp ℝ 2 μ}
    (hv : AEStronglyMeasurable[m] v μ) :
    AEStronglyMeasurable[m]
      ((unitary μ σ (hσ.mono hm le_rfl) hne).symm v) (weightedMeasure μ σ) := by
  have hvs : AEStronglyMeasurable[m] (fun ω => v ω / σ ω) (weightedMeasure μ σ) :=
    (hv.div₀ hσ.stronglyMeasurable.aestronglyMeasurable).mono_ac
      (weightedMeasure_absolutelyContinuous μ σ)
  exact hvs.congr (unitary_symm_coeFn μ σ (hσ.mono hm le_rfl) hne v).symm

theorem unitary_mem_lpMeas_iff (u : Lp ℝ 2 (weightedMeasure μ σ)) :
    unitary μ σ (hσ.mono hm le_rfl) hne u ∈ lpMeas ℝ ℝ m 2 μ ↔
      u ∈ lpMeas ℝ ℝ m 2 (weightedMeasure μ σ) := by
  simp only [mem_lpMeas_iff_aestronglyMeasurable]
  constructor
  · intro hu
    simpa only [LinearIsometryEquiv.symm_apply_apply] using
      aestronglyMeasurable_unitary_symm m μ σ hm hσ hne hu
  · exact aestronglyMeasurable_unitary m μ σ hm hσ hne

/-- The actual weighted unitary restricted to the sub-sigma-algebra's L² spaces. -/
def measurableUnitary :
    lpMeas ℝ ℝ m 2 (weightedMeasure μ σ) ≃ₗᵢ[ℝ] lpMeas ℝ ℝ m 2 μ where
  toFun := fun u => ⟨unitary μ σ (hσ.mono hm le_rfl) hne u,
    (unitary_mem_lpMeas_iff m μ σ hm hσ hne u).mpr u.property⟩
  invFun := fun v => ⟨(unitary μ σ (hσ.mono hm le_rfl) hne).symm v,
    mem_lpMeas_iff_aestronglyMeasurable.mpr
      (aestronglyMeasurable_unitary_symm m μ σ hm hσ hne
        (mem_lpMeas_iff_aestronglyMeasurable.mp v.property))⟩
  left_inv := fun u => Subtype.ext ((unitary μ σ (hσ.mono hm le_rfl) hne).symm_apply_apply u)
  right_inv := fun v => Subtype.ext ((unitary μ σ (hσ.mono hm le_rfl) hne).apply_symm_apply v)
  map_add' := fun u v => Subtype.ext ((unitary μ σ (hσ.mono hm le_rfl) hne).map_add u v)
  map_smul' := fun r u => Subtype.ext ((unitary μ σ (hσ.mono hm le_rfl) hne).map_smul r u)
  norm_map' := fun u => (unitary μ σ (hσ.mono hm le_rfl) hne).norm_map u

theorem measurableUnitary_coe (u : lpMeas ℝ ℝ m 2 (weightedMeasure μ σ)) :
    (measurableUnitary m μ σ hm hσ hne u : Lp ℝ 2 μ) =
      unitary μ σ (hσ.mono hm le_rfl) hne u := rfl

theorem measurableUnitary_symm_coe (v : lpMeas ℝ ℝ m 2 μ) :
    ((measurableUnitary m μ σ hm hσ hne).symm v : Lp ℝ 2 (weightedMeasure μ σ)) =
      (unitary μ σ (hσ.mono hm le_rfl) hne).symm v := rfl

theorem measurableUnitary_coeFn (u : lpMeas ℝ ℝ m 2 (weightedMeasure μ σ)) :
    (measurableUnitary m μ σ hm hσ hne u : Lp ℝ 2 μ) =ᵐ[μ]
      fun ω => σ ω * (u : Lp ℝ 2 (weightedMeasure μ σ)) ω :=
  unitary_coeFn μ σ (hσ.mono hm le_rfl) hne u

theorem measurableUnitary_symm_coeFn (v : lpMeas ℝ ℝ m 2 μ) :
    ((measurableUnitary m μ σ hm hσ hne).symm v : Lp ℝ 2 (weightedMeasure μ σ))
      =ᵐ[weightedMeasure μ σ] fun ω => (v : Lp ℝ 2 μ) ω / σ ω :=
  unitary_symm_coeFn μ σ (hσ.mono hm le_rfl) hne v

end OperatorDerivativeRewrite.Foundation.WeightedMeasurableTransport
