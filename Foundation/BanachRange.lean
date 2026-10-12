import Foundation.BanachLpAdjoint
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Range and annihilator results for the bounded Banach derivative

All statements concern an actual continuous linear map into scalar `Lp`.
The lower-bound hypotheses in the range results are explicit analytic estimates,
not a claim that any particular stochastic integral satisfies them.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace OperatorDerivativeRewrite.Foundation.BanachRange

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p q : ℝ≥0∞}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p]

private def pairing (F : Lp ℝ q μ) : Lp ℝ p μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p F

/-- A positive lower norm estimate forces injectivity. -/
theorem injective_of_lower_bound (δ : H →L[ℝ] Lp ℝ p μ)
    (c : ℝ) (hc : 0 < c) (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) :
    Function.Injective δ := by
  intro u v huv
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hzero : δ (u - v) = 0 := by simp [map_sub, huv]
  have hcu := hδ (u - v)
  rw [hzero, norm_zero] at hcu
  exact le_antisymm (nonpos_of_mul_nonpos_right hcu hc) (norm_nonneg _)

/-- An inverse-norm estimate is a concrete anti-Lipschitz estimate. -/
theorem antilipschitz_of_inverse_bound (δ : H →L[ℝ] Lp ℝ p μ)
    (K : ℝ≥0) (hδ : ∀ u : H, ‖u‖ ≤ K * ‖δ u‖) :
    AntilipschitzWith K δ := by
  apply AntilipschitzWith.of_le_mul_dist
  intro u v
  simpa only [dist_eq_norm, map_sub] using hδ (u - v)

/-- A norm-bounded inverse on the range forces that range to be closed. -/
theorem isClosed_range_of_inverse_bound [CompleteSpace H]
    (δ : H →L[ℝ] Lp ℝ p μ)
    (K : ℝ≥0) (hδ : ∀ u : H, ‖u‖ ≤ K * ‖δ u‖) :
    IsClosed (Set.range δ) :=
  (antilipschitz_of_inverse_bound δ K hδ).isClosed_range δ.uniformContinuous

/-- The familiar positive lower bound gives an explicit inverse-norm bound. -/
theorem inverse_bound_of_lower_bound (δ : H →L[ℝ] Lp ℝ p μ)
    (c : ℝ) (hc : 0 < c) (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖)
    (u : H) :
    ‖u‖ ≤ c⁻¹ * ‖δ u‖ := by
  have h := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hδ u)
  simpa [div_eq_mul_inv, mul_comm] using h

/-- A positive lower estimate and completeness imply a closed range. -/
theorem isClosed_range_of_lower_bound [CompleteSpace H]
    (δ : H →L[ℝ] Lp ℝ p μ)
    (c : ℝ) (hc : 0 < c) (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) :
    IsClosed (Set.range δ) := by
  let K : ℝ≥0 := ⟨c⁻¹, le_of_lt (inv_pos.mpr hc)⟩
  apply isClosed_range_of_inverse_bound δ K
  intro u
  exact inverse_bound_of_lower_bound δ c hc hδ u

/-- A complete domain and a genuine lower estimate give a continuous inverse
on the actual range, supplied by Mathlib's Banach inverse theorem. -/
def rangeEquiv [CompleteSpace H]
    (δ : H →L[ℝ] Lp ℝ p μ)
    (c : ℝ) (hc : 0 < c) (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) :
    H ≃L[ℝ] δ.range :=
  δ.equivRange (injective_of_lower_bound δ c hc hδ)
    (isClosed_range_of_lower_bound δ c hc hδ)

/-- Recovery on the range has the same quantitative bound as the original
lower estimate. No representation of arbitrary `Lp` elements is claimed. -/
theorem rangeEquiv_symm_bound [CompleteSpace H]
    (δ : H →L[ℝ] Lp ℝ p μ)
    (c : ℝ) (hc : 0 < c) (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖)
    (v : δ.range) :
    c * ‖(rangeEquiv δ c hc hδ).symm v‖ ≤ ‖v‖ := by
  rcases v with ⟨v, ⟨u, rfl⟩⟩
  simpa [rangeEquiv] using hδ u

/-- The kernel annihilates the norm closure of the range, not just its points. -/
theorem kernel_annihilates_closure (δ : H →L[ℝ] Lp ℝ p μ)
    (F : Lp ℝ q μ)
    (hF : BanachLpAdjoint.boundedBanachDerivative δ F = 0)
    {v : Lp ℝ p μ} (hv : v ∈ closure (Set.range δ)) :
    ∫ ω, F ω * v ω ∂μ = 0 := by
  let L : Lp ℝ p μ →L[ℝ] ℝ := pairing F
  have hclosed : IsClosed {w : Lp ℝ p μ | L w = 0} :=
    isClosed_eq L.continuous continuous_const
  have hrange : Set.range δ ⊆ {w : Lp ℝ p μ | L w = 0} := by
    rintro w ⟨u, rfl⟩
    change L (δ u) = 0
    simpa only [L, pairing, ContinuousLinearMap.lpPairing_eq_integral,
      ContinuousLinearMap.mul_apply'] using
      (BanachLpAdjoint.boundedBanachDerivative_eq_zero_iff δ F).mp hF u
  have hzero := (closure_minimal hrange hclosed) hv
  change L v = 0 at hzero
  simpa only [L, pairing, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply'] using hzero

/-- Vanishing on the range and vanishing on its closure are equivalent. -/
theorem kernel_iff_annihilates_closure (δ : H →L[ℝ] Lp ℝ p μ)
    (F : Lp ℝ q μ) :
    BanachLpAdjoint.boundedBanachDerivative δ F = 0 ↔
      ∀ v ∈ closure (Set.range δ), ∫ ω, F ω * v ω ∂μ = 0 := by
  constructor
  · intro hF v hv
    exact kernel_annihilates_closure δ F hF hv
  · intro hF
    apply (BanachLpAdjoint.boundedBanachDerivative_eq_zero_iff δ F).mpr
    intro u
    exact hF (δ u) (subset_closure ⟨u, rfl⟩)

/-- A nonzero actual pairing separates a candidate from the closed range. -/
theorem not_mem_closure_of_pairing_ne_zero (δ : H →L[ℝ] Lp ℝ p μ)
    (F : Lp ℝ q μ) (v : Lp ℝ p μ)
    (hF : BanachLpAdjoint.boundedBanachDerivative δ F = 0)
    (hpair : (∫ ω, F ω * v ω ∂μ) ≠ 0) :
    v ∉ closure (Set.range δ) := by
  intro hv
  exact hpair (kernel_annihilates_closure δ F hF hv)

/-- A genuine annihilator with a nonzero self-pairing proves nonrepresentability. -/
theorem not_mem_range_of_pairing_ne_zero (δ : H →L[ℝ] Lp ℝ p μ)
    (F : Lp ℝ q μ) (v : Lp ℝ p μ)
    (hF : BanachLpAdjoint.boundedBanachDerivative δ F = 0)
    (hpair : (∫ ω, F ω * v ω ∂μ) ≠ 0) :
    v ∉ Set.range δ := by
  intro hv
  exact not_mem_closure_of_pairing_ne_zero δ F v hF hpair (subset_closure hv)

end OperatorDerivativeRewrite.Foundation.BanachRange
